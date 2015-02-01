{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

import Numeric
import Data.Function
import Data.Monoid
import Data.Maybe
import Data.IORef
import Data.Time.Clock
import Data.Vect
import Data.Bits
import Data.PriorityQueue.FingerTree as Q
import qualified Data.Map as Map
import qualified Data.IntMap as IMap
import qualified Data.Trie as T
import qualified Data.Vector.Storable as SV
import qualified Data.Vector.Storable as V
import Control.Applicative hiding (Const)
import Control.Monad
import System.Random
import System.Environment

import "GLFW-b" Graphics.UI.GLFW as GLFW
import LambdaCube.GL
import LambdaCube.GL.Mesh
import LambdaCube.Font.Atlas
import LambdaCube.Font.Common hiding (floatF,floatV,v3v4)
import qualified LambdaCube.Font.SimpleDistanceField as SDF
import qualified LambdaCube.Font.CompositeDistanceField as CDF
import Graphics.Text.TrueType

import Prelude hiding (Rational)
type Rational = Double

--------------------------------------------------------------------------------

newtype Corner = Corner_ Int    -- left lower corner
    deriving (Eq, Ord, Show)

type Cell = Corner

ix :: Corner -> Int
ix (Corner_ x) = x

ce :: Cell -> (Int, Int)
ce (Corner_ x) = (x `shiftR` 8, x .&. 255)

pattern Corner x y <- (ce -> (x, y))

cell x y = Corner_ $ (x `shiftL` 8) .|. y

--------------------

type Size = (Int, Int) -- width, height

data Dir = Horiz | Vert
    deriving (Eq, Ord, Show)

data Wall = Wall Dir Corner
    deriving (Eq, Ord, Show)

type Walls = Map.Map Wall (Maybe Rational)
type Cells = IMap.IntMap Rational

type Time' = Rational

-------------------------------------------------------------------------------- infection

neighbours :: Size -> Cell -> [(Wall, Cell)]
neighbours (w, h) c@(Corner x y) =
    [ (Wall Horiz c, cell x $ (y-1) `mod` h)
    , (Wall Horiz $ cell x $ (y+1) `mod` h, cell x $ (y+1) `mod` h)
    , (Wall Vert c, cell ((x-1) `mod` h) y)
    , (Wall Vert $ cell ((x+1) `mod` h) y, cell ((x+1) `mod` h) y)
    ]

compute
    :: Size     -- size of the map
    -> (Wall -> Maybe Rational)    -- neighbours with thickness
    -> PQueue Time' (Cell, Cell)    -- priority queue of exploding neighbours
    -> Time'     -- current time
    -> Cells    -- already infected cells with infection time
    -> Cells    -- cells in danger, from when
    -> (Time', Cells, Cells)    -- time to infect; infected cells with infection time
compute s ws q t cs dcs = case minViewWithKey q of
    Nothing -> (t, cs, dcs)
    Just ((t', (c, c')), q)
        | IMap.member (ix c') cs -> compute s ws q t cs dcs
        | otherwise -> compute s ws q' t' cs' dcs'
          where
            cs' = IMap.insert (ix c') t' cs
            newws = filter ((/=c) . snd) $ neighbours s c'
            qq = mkQueue ws t' c' newws
            dcs' = foldr (\k -> IMap.insertWith (\_ kk -> kk) (ix k) t') dcs $ map (snd . snd) qq
            q' = foldr (\(k,v) -> Q.insert k v) q qq

mkQueue ws t c newws = [(t + t', (c, c')) | (w, c') <- newws, Just t' <- return $ ws w]

compute' :: Size -> Walls -> Cell -> (Time', Cells, Cells)
compute' s@(wi,he) ws c = compute s f q t (IMap.singleton (ix c) t) $ IMap.insert (ix c) (-1) $ IMap.fromList $ zip (map (ix . snd . snd) qq) $ repeat t
  where
    t = 0
    newws = neighbours s c
    q = foldr (\(k,v) -> Q.insert k v) Q.empty qq
    qq = mkQueue f t c newws
    f w = case w of
        Wall Horiz p -> fromMaybe (Just 0) $ IMap.lookup (ix p) arrh
        Wall Vert  p -> fromMaybe (Just 0) $ IMap.lookup (ix p) arrv
    arrh = IMap.fromList [(ix p, d) | (Wall Horiz p, d) <- Map.toList ws]
    arrv = IMap.fromList [(ix p, d) | (Wall Vert p, d) <- Map.toList ws]

cskk size@(w,h) ws init = (t, map (/t) $ ff 2 cs_, map (/t) $ ff 2 dcs)
  where
    (t, cs_, dcs) = compute' size ws init
    ff v d = [fromMaybe v $ IMap.lookup (ix $ cell x y) d | x <- [0..w-1], y <- [0..h-1]]

-------------------------------------------------------------------------------- wall creation

data WallD
    = Empty
    | Union UFun WallD WallD
    | Grad (Rational -> Rational -> Rational)
    | Distort (Rational -> Rational) WallD
    | Fill WallD WallL
    | Path (Double -> (Double, Double))

data UFun = Fst | Snd | Add

data WallL
    = Rand
    | Co (Maybe Rational)
    | GradL (Rational -> Rational)

instance Monoid WallD where
    mempty = Empty
    mappend = Union Snd

loop (x:xs) = segments (x:xs ++ [x])

segments xs = foldr1 addP $ zipWith line xs (tail xs)

line (x1, y1) (x2, y2) t = (x1 + t * (x2 - x1), y1 + t * (y2 - y1))

addP p1 p2 t
    | t < 0.5   = p1 $ 2 * t
    | otherwise = p2 $ 2 * (t - 0.5)

compile :: WallD -> Size -> IO Walls
compile Empty _ = return mempty
compile (Union f a b) s = liftA2 (Map.unionWith $ unionFun f) (compile a s) (compile b s)
compile (Distort f w) s = Map.map (fmap f) <$> compile w s
compile (Fill w ds) s = compile w s >>= \w -> Map.fromList . zip (Map.keys w) <$> compileL ds (Map.size w)
compile (Path pa) (w, h) = return $ Map.fromList $ zip (f 0 1) (repeat Nothing)
  where
    f b e
        | p == q && r `elem` [p, q] = []
        | Just w <- wall p q, r `elem` [p, q] = [w]
        | otherwise = f b x ++ f x e
      where
        p = tr b
        q = tr e
        r = tr x
        x = (b + e) / 2
    wall :: Corner -> Corner -> Maybe Wall
    wall (Corner i1 j1) (Corner i2 j2) | i1 == i2 && abs (j1 - j2) == 1 = Just $ Wall Vert  $ cell (i1 `mod` w) (min j1 j2 `mod` h)
    wall (Corner i1 j1) (Corner i2 j2) | j1 == j2 && abs (i1 - i2) == 1 = Just $ Wall Horiz $ cell (min i1 i2 `mod` h) (j1 `mod` h)
    wall _ _ = Nothing
    tr t = cell (round $ (x + 0.5) * fromIntegral w) (round $ (y + 0.5) * fromIntegral h)
      where (x, y) = pa t

compile (Grad f) (w, h) = return $ Map.fromList $
               [(Wall Horiz (cell x y), Just v) | x <- [0..w-1], y <- [0..h-1], Just v <- return $ g (x, y) (x, y-1) ]
            ++ [(Wall Vert  (cell x y), Just v) | x <- [0..w-1], y <- [0..h-1], Just v <- return $ g (x, y) (x-1, y) ]
  where
    g p q = if a == b then Nothing else Just $ abs $ a - b
      where
        a = tr p
        b = tr q
    tr (i, j) = f ((fromIntegral i + 0.5) / fromIntegral w - 0.5) ((fromIntegral j + 0.5) / fromIntegral h - 0.5)

compileL :: WallL -> Int -> IO [Maybe Rational]
compileL Rand n = replicateM n $ randomRIO (0, 1000) <&> \x -> Just $ fromIntegral (x :: Int) / 1000
compileL (Co x) n = return $ replicate n x
compileL (GradL f) n = return [Just $ f $ (fromIntegral i + 0.5) / fromIntegral n | i <- [0..n-1]]

unionFun = \case
    Fst -> const
    Snd -> const id
    Add -> liftA2 (+)

newws size lev = compile (levels !! (lev `mod` length levels)) size

levels :: [WallD]
levels =
    [ bound $ flat <> Grad const
    , bound $ flat <> Grad (const id)
    , flat <> Grad (max `on` abs)
    , flat <> Grad (min `on` abs)
    , bound $ Grad (+)
    , flat .* 0.005 <> Grad (min `on` abs)
    , Fill flat (co 0.1) <> Grad (max `on` abs)
    , bound $ randWalls'
    , let b = 30 in Fill flat (co 0.01) <> Fill (Path (\t -> (0.5 * t * sin (b * t), 0.5 * t * cos (b * t)))) (co 1)
    , gradD (\x y -> sin (4*pi*y) + sin (4*pi*x))
    , bound $ flat <> gradD (\x y -> sin (4*pi*x))
    , gradD ((((**0.25) .) . (+)) `on` (**2))
    , gradD ((((**0.5) .) . (+)) `on` (**2))
    , Grad ((+) `on` (^2))
    , randWalls' .* 0.5 <> Grad (min `on` abs)
    ]
  where
    gradD :: (Double -> Double -> Double) -> WallD
    gradD f = Grad (((realToFrac .) . f) `on` realToFrac)
    randWalls' = Distort ((* 5) . (^ 4)) randWalls
    randWalls = Fill (Grad (+)) Rand
    flat = Fill (Grad (+)) (Co $ Just 0)

    bound = (<> Path (loop [(0.5, 0.5), (0.5, -0.5), (-0.5,-0.5), (-0.5, 0.5)]))
    co = Co . Just

    x .* t = Fill x (co t)
    infixl 7 .*

levelSpeed :: Int -> Rational
levelSpeed = (100/) . (+40) . fromIntegral

------------------------------------

texturing :: Exp Obj (VertexStream Triangle (V3F,Float,Float)) -> Exp Obj (FrameBuffer 1 (Float,V4F))
texturing objs = Accumulate fragmentCtx PassAll fragmentShader fragmentStream emptyFB
  where
    rasterCtx :: RasterContext Triangle
    rasterCtx = TriangleCtx (CullNone) PolygonFill NoOffset LastVertex

    fragmentCtx :: AccumulationContext (Depth Float :+: (Color (V4 Float) :+: ZZ))
    fragmentCtx = AccumulationContext Nothing $ DepthOp Less True:.ColorOp NoBlending (one' :: V4B):.ZT

    emptyFB :: Exp Obj (FrameBuffer 1 (Float,V4F))
    emptyFB = FrameBuffer (DepthImage n1 1000:.ColorImage n1 (V4 0 0 0 1):.ZT)

    fragmentStream :: Exp Obj (FragmentStream 1 (Float))
    fragmentStream = Rasterize rasterCtx primitiveStream

    primitiveStream :: Exp Obj (PrimitiveStream Triangle () 1 V (Float))
    primitiveStream = Transform vertexShader objs

    vertexShader :: Exp V (V3F,Float,Float) -> VertexOut () (Float)
    vertexShader puv = VertexOut v4 (Const 1) ZT (Flat col:.ZT)
      where
        v4 :: Exp V V4F
        v4 = v3v4' p
        (p,beg,end) = untup3 puv
        col = min' (c 1) $ max' (c 0) ((t @- beg) @/ (end @- beg))

        t :: Exp V Float
        t = Uni (IFloat "time")

        v3v4' :: Exp V V3F -> Exp V V4F
        v3v4' v = let V3 x y z = unpack' v in pack' $ V4 (x @* c 0.99) (y @* c 0.99) (z) (Const 1)

    fragmentShader :: Exp F (Float) -> FragmentOut (Depth Float :+: Color V4F :+: ZZ)
    fragmentShader dist = FragmentOutRastDepth $ pack' (V4 dist dist (Const 0) (Const 1)) :. ZT

c :: Float -> Exp V Float
c = Const

useCompositeDistanceField = True
textStyle = defaultTextStyle { textLetterSpacing = 0.0, textLineHeight = 1.25 }
fontOptions = defaultOptions { atlasSize = 600, atlasLetterPadding = 2 }

main :: IO ()
main = do
    args <- getArgs
    let
        res = case args of
            [] -> 32
            [x] -> read x
        size :: Size
        size = (res, res)

        (wi, he) = size

        (ll, sizeD) = (x, (w * x, h * x))
          where
            (fromIntegral -> w, fromIntegral -> h) = size
            x = 1 / min w h

        totalsize = fst size * snd size

        cube :: Mesh
        cube = Mesh
            { mAttributes   = T.fromList
                [ ("vertexPosition_modelspace", A_V3F $ SV.fromList [V3 x y z | (x,y,z) <- g_vertex_buffer_data])
                , ("vertexBegin",               A_Float $ SV.fromList $ replicate (6 * totalsize) 0)
                , ("vertexEnd",                 A_Float $ SV.fromList $ replicate (6 * totalsize) 0)
                ]
            , mPrimitive    = P_Triangles
            , mGPUData      = Nothing
            }
          where
            g_vertex_buffer_data = flip concatMap (liftA2 (,) [0..wi-1] [0..he-1]) $ \(fromIntegral -> x, fromIntegral -> y) ->
                map (\(a,b,c) -> ((a+x)*ll*2-1, (b+y)*ll*2-1, c))
                [ ( 1.0, 1.0, 0)
                , ( 1.0,   0, 0)
                , (   0,   0, 0)
                , ( 1.0, 1.0, 0)
                , (   0,   0, 0)
                , (   0, 1.0, 0)
                ]

    GLFW.init
    defaultWindowHints
    mapM_ windowHint
      [ WindowHint'ContextVersionMajor 3
      , WindowHint'ContextVersionMinor 3
      , WindowHint'OpenGLProfile OpenGLProfile'Core
      , WindowHint'OpenGLForwardCompat True
      ]
    Just win <- createWindow 600 600 "LambdaCube 3D GameJam - Infection" Nothing Nothing
    makeContextCurrent $ Just win

    renderer <- compileRenderer $ ScreenOut $
        PrjFrameBuffer "" tix0 $ textRender $ texToFB $ imgToTex $ 
        PrjFrameBuffer "" tix0 $ texturing $ 
        Fetch "stream" Triangles (IV3F "vertexPosition_modelspace", IFloat "vertexBegin", IFloat "vertexEnd")
    initUtility renderer
    setScreenSize renderer 600 600

    -- text
    Right font <- loadFontFile "Orbitron-Bold.ttf"
    let fontRenderer = if useCompositeDistanceField then CDF.fontRenderer else SDF.fontRenderer
        letterScale = 72
    atlas <- createFontAtlas font fontRenderer fontOptions { atlasLetterScale = letterScale }

    let showInit msg = do
            textMesh <- buildTextMesh atlas textStyle msg
            textBuffer <- compileMesh textMesh
            o <- addMesh renderer "textMesh" textBuffer [] --["textTransform","textAlpha"]
        --    let textUniforms = objectUniformSetter o
            let textUniforms = uniformSetter renderer
                uniforms = uniformSetter renderer
                letterScale = atlasLetterScale (atlasOptions atlas)
                letterPadding = atlasLetterPadding (atlasOptions atlas)
                scale = 0.1
                ofsX = -0.85
                ofsY = 0.70
            uniformFTexture2D "fontAtlas" uniforms (getTextureData atlas)
            uniformFloat "textAlpha" uniforms 0.8

            uniformM33F "textTransform" uniforms (V3 (V3 (scale * 0.75) 0 0) (V3 0 scale 0) (V3 ofsX ofsY 1))
            uniformFloat "outlineWidth" uniforms (min 0.5 (fromIntegral letterScale / (120 * fromIntegral letterPadding * scale * sqrt 2 * 0.75)))
            return $ enableObject o False

    let uniformMap      = uniformSetter renderer
        setWindowSize   = setScreenSize renderer
        tm  = uniformFloat "time" uniformMap
        scale = 0.1

    setWindowSize 600 600

    gpuCube <- compileMesh cube
    addMesh renderer "stream" gpuCube []

    let setw xs ys = do
            updateMesh gpuCube [("vertexBegin", A_Float $ SV.fromList 
                $ concatMap (replicate 6) xs)] Nothing
            updateMesh gpuCube [("vertexEnd", A_Float $ SV.fromList 
                $ concatMap (replicate 6) ys)] Nothing

    let getPos = do
            (cx, cy) <- getCursorPos win
            let fl i x = min (i-1) $ floor $ fromIntegral i * x / 600
            return (fl (fst size) cx, fl (snd size) (600 - cy))

    txt <- showInit $ unlines
        [ "Infect the tissue with one mouse click."
        , ""
        , "This is the test run,"
        , "click anywhere to test the tissue."
        ]
    xxr <- newIORef $ Wait 0 txt Nothing
    tm $! 0
    let callb _ MouseButton'1 MouseButtonState'Pressed _ = do
            xx <- readIORef xxr
            case xx of
              Wait lev cl res -> do
                (cx, cy) <- getPos
                ws <- maybe (newws size lev) (return . snd) res
                let (t, ds, dcs) = cskk size ws $ cell cx cy
                let xx = map realToFrac ds
                let xx' = map realToFrac dcs
                setw xx' xx
                cl' <- case res of
                    Nothing -> do
                        cl
                        showInit "Test infection."
                    Just _ -> return cl
                curTime <- getCurrentTime
                writeIORef xxr $ Do lev cl' curTime t ws xx $ fst <$> res
                return ()
              _ -> return ()
        callb _ _ _ _ = return ()

    setMouseButtonCallback win $ Just callb

    let keyIsPressed k = fmap (==KeyState'Pressed) $ getKey win k
        loop = do
            mode <- readIORef xxr
            case mode of
              Wait{} -> do
                (cx, cy) <- getPos
                let v = cx * snd size + cy
                    upd i x xs = take i xs ++ x: drop (i+1) xs
                setw (upd v (-1) $ replicate totalsize 0) (upd v 0 $ replicate totalsize 1)
              Do lev cl startTime sp ws xx res -> do
                curTime <- getCurrentTime
                let sp' = maybe (levelSpeed lev) (\(_, old) -> sp / old * levelSpeed lev) res
                let t = realToFrac (curTime `diffUTCTime` startTime) / realToFrac sp'
                if t > 1 then do
                  cl
                  tm $! 0
                  case res of
                    Nothing -> do
                        faster <- randomIO
                        txt <- showInit $ ("Infected in " ++) . showFFloat (Just 2) (realToFrac sp') . (" sec\n\nTry to infect " ++)
                                $ (if faster then "faster" else "slower") ++ " the same tissue!"
                        writeIORef xxr $ Wait lev txt $ Just ((faster, sp), ws)
                    Just (faster, old) -> do
                        let ok = if faster then sp < old else sp > old
                            lev' = if ok then lev + 1 else max 0 (lev - 1)
                        txt <- showInit $ ("1) " ++) . showFFloat (Just 2) (realToFrac $ levelSpeed lev) . (" sec\n2) " ++)
                                    . showFFloat (Just 2) (realToFrac sp') $
                                    " sec\n\n" ++ (if ok then "Great!" else "Failed attempt.")
                                    ++ "\n\nYou are at level " ++ show lev' ++ " now."
                                    ++ "\nClick to test infection."
                        writeIORef xxr $ Wait lev' txt Nothing
                  else
                    tm $! t

            render renderer
            swapBuffers win >> pollEvents

            k <- keyIsPressed Key'Escape
            unless k $ loop

    loop

    dispose renderer
    destroyWindow win
    terminate

data Mode
    = Wait Level (IO ()) (Maybe ((Bool, Rational), Walls))
    | Do Level (IO ()) UTCTime Rational Walls [Float] (Maybe (Bool, Rational))

type Level = Int

-------------------------------------------------------------------------------- utils

infixl 1 <&>
(<&>) = flip (<$>)

a `between` (c, d) = c <= a && a <= d
infix 4 `between`

vec4ToV4F :: Vec4 -> V4F
vec4ToV4F (Vec4 x y z w) = V4 x y z w

mat4ToM44F :: Mat4 -> M44F
mat4ToM44F (Mat4 a b c d) = V4 (vec4ToV4F a) (vec4ToV4F b) (vec4ToV4F c) (vec4ToV4F d)

textRender :: Exp Obj (FrameBuffer 1 V4F) -> Exp Obj (FrameBuffer 1 V4F)
textRender = renderText
  where
    renderText = Accumulate textFragmentCtx PassAll textFragmentShader textFragmentStream
    rasterCtx = TriangleCtx CullNone PolygonFill NoOffset LastVertex

    textFragmentCtx = AccumulationContext Nothing (ColorOp textBlending (V4 True True True True) :. ZT)
    textBlending = Blend (FuncAdd, FuncAdd) ((One, One), (OneMinusSrcAlpha, One)) zero'
    textFragmentStream = Rasterize rasterCtx textStream
    textStream = Transform vertexShader (Fetch "textMesh" Triangles (IV2F "position", IV2F "uv"))

    vertexShader attr = VertexOut point (floatV 1) ZT (Smooth uv :. ZT)
      where
        point = v3v4 (transform @*. v2v3 pos)
        transform = Uni (IM33F "textTransform") :: Exp V M33F
        (pos, uv) = untup2 attr

    textFragmentShader uv = FragmentOut (pack' (V4 result result result result) @* fade :. ZT)
      where
        fade = Uni (IFloat "textAlpha") :: Exp F Float
        result = step distance
        distance = case useCompositeDistanceField of
            False -> SDF.sampleDistance "fontAtlas" uv
            True -> CDF.sampleDistance "fontAtlas" uv
        step = smoothstep' (floatF 0.5 @- outlineWidth) (floatF 0.5 @+ outlineWidth)
        outlineWidth = Uni (IFloat "outlineWidth") :: Exp F Float

texToFB tex = renderScreen' frag
  where
    frag :: Exp F V2F -> FragmentOut (Color V4F :+: ZZ)
    frag uv = FragmentOut $ color tex uv :. ZT

    color t uv = texture' (smp t) uv
    smp t = Sampler LinearFilter ClampToEdge t

imgToTex img = Texture (Texture2D (Float RGBA) n1) (V2 sizeI sizeI) NoMip [img]
 where
  sizeI = 600 :: Word32

renderScreen' :: (Exp F V2F -> FragmentOut (Color V4F :+: ZZ)) -> Exp Obj (FrameBuffer 1 V4F)
renderScreen' frag = Accumulate fragCtx PassAll frag rast clear
  where
    fragCtx = AccumulationContext Nothing $ ColorOp NoBlending (one' :: V4B):.ZT
    clear   = FrameBuffer (ColorImage n1 (V4 0 0 0 0):.ZT)
    rast    = Rasterize triangleCtx prims
    prims   = Transform vert input
    input   = Fetch "ScreenQuad" Triangles (IV2F "position")

    vert :: Exp V V2F -> VertexOut () V2F
    vert uv = VertexOut v4 (Const 1) ZT (NoPerspective uv':.ZT)
      where
        v4      = pack' $ V4 u v (floatV 1) (floatV 1)
        V2 u v  = unpack' uv
        uv'     = uv @* floatV 0.5 @+ floatV 0.5

floatV :: Float -> Exp V Float
floatV = Const

floatF :: Float -> Exp F Float
floatF = Const

v3v4 :: Exp s V3F -> Exp s V4F
v3v4 v = let V3 x y z = unpack' v in pack' $ V4 x y z (Const 1)

initUtility :: Renderer -> IO ()
initUtility renderer = do
    let setMesh n m = compileMesh m >>= (\cm -> addMesh renderer n cm [])
    _ <- setMesh "ScreenQuad" quad
    return ()

quad :: Mesh
quad = Mesh
    { mAttributes = T.singleton "position" $ A_V2F $ V.fromList [-1 ^ 1, -1 ^ -1, 1 ^ -1, 1 ^ -1, 1 ^ 1, -1 ^ 1]
    , mPrimitive = P_Triangles
    , mGPUData = Nothing
    }
  where
    infixr 0 ^
    (^) = V2


