
module Hata.Runtime.UI.Test where

{-# LANGUAGE PatternSynonyms, OverloadedStrings #-}

-- original author:
--    Mirco "MacSlow" Mueller <macslow@bangang.de>
--
-- created:
--    10.1.2006 (or so)
--
-- http://www.gnu.org/licenses/licenses.html#GPL
--
-- ported to Haskell by:
--    Duncan Coutts <duncan.coutts@worc.ox.ac.uk>
--
-- updated to GTK 3 by Catherine Holloway
-- converted to Haskell GI by Kilian Kilger
--

import qualified GI.Cairo
import qualified GI.Gdk as GDK
import qualified GI.Gtk as GTK
-- import qualified GI.Gdk.Objects.Window as GDK
-- import GI.GLib (pattern PRIORITY_DEFAULT, timeoutAdd)
import GI.GLib -- (PRIORITY_DEFAULT, timeoutAdd)
import GI.Cairo.Render.Connector (renderWithContext)
import GI.Cairo.Render
import GI.Cairo.Render.Types
import qualified GI.Cairo.Render.Internal as Internal
import Data.Time
import Control.Monad (when)
import Data.Maybe (isJust)
import Data.IORef
import Data.Text as Text
import Data.Maybe (fromMaybe)
import Data.HashMap.Strict as H

import Hata.Runtime.Application.Render.Definition
import qualified GI.Cairo.Render.Types as Internal

type DrawState = HashMap Text Extent

setCairoState :: BaseItem -> Render ()
setCairoState (StringBI (RGB r g b) size s) = do
  selectFontFace "MxFont" FontSlantNormal FontWeightNormal
  setSourceRGB (fromIntegral r / 255) (fromIntegral g / 255) (fromIntegral b / 255)
  setFontSize (fromIntegral size)
setCairoState (RectangleBI (RGB r g b) size) = do
  setSourceRGB (fromIntegral r / 255) (fromIntegral g / 255) (fromIntegral b / 255)

renderItem :: Item -> Render ()
renderItem (Item loc a) = do
  save
  setCairoState a
  render a
  restore
    where (x,y) = fromRationalCoord loc
          render (StringBI _ _ s) = do
              moveTo x y
              showText s
          render (RectangleBI _ s) = do
            let (w,h) = fromRationalCoord s
            rectangle x y w h
            fill

computeExtent :: BaseItem -> Render (Extent)
computeExtent (StringBI _ _ s) = do
  ex <- textExtents s
  let (x,y) = (textExtentsXadvance ex , textExtentsYadvance ex)
  return $ toRationalCoord (x,y)
computeExtent (RectangleBI _ s) = pure s

stateCommand :: GTK.IsWidget widget => widget
             -> IORef DrawState
             -> StateCmd Text BaseItem
             -> Render ()
stateCommand canvas drawRef ClearAll = liftIO $ modifyIORef' drawRef (\_ -> H.empty)
stateCommand canvas drawRef (Clear n) = liftIO $ modifyIORef' drawRef (H.delete n)
stateCommand canvas drawRef (Set n x) = do

  -- We compute the extent of an item
  save
  setCairoState x
  ex <- computeExtent x
  restore

  -- We save the extent in the hashmap
  liftIO $ modifyIORef' drawRef (H.insert n ex)


drawCommand :: GTK.IsWidget widget => widget
             -> IORef DrawState
             -> Cmd
             -> Render ()
drawCommand canvas drawRef (DoChangeState scmd) = stateCommand canvas drawRef scmd
drawCommand canvas drawRef (DoRender getItems) = do

  width  <- liftIO $ GTK.widgetGetAllocatedWidth  canvas
  height <- liftIO $ GTK.widgetGetAllocatedHeight canvas

  drawState <- liftIO $ readIORef drawRef
  let items = getItems (\a -> case drawState !? a of
                           Just x -> Right x
                           Nothing -> Left ())
                       (((fromIntegral width,1),(fromIntegral height,1)))
  mapM renderItem items
  return ()

drawCommands :: GTK.IsWidget widget => widget
             -> IORef DrawState
             -> IORef a -> (a -> [Cmd])
             -> Render Bool
drawCommands canvas drawStateRef stateRef getCmds = do

  state <- liftIO $ readIORef stateRef
  let cmds = getCmds state
  mapM (drawCommand canvas drawStateRef) cmds

  return True

drawMyLine :: GTK.IsWidget widget => widget -> Render ()
drawMyLine canvas = do

  width  <- liftIO $ GTK.widgetGetAllocatedWidth  canvas
  height <- liftIO $ GTK.widgetGetAllocatedHeight canvas
  save
  scale (fromIntegral width) (fromIntegral height)

  save
  setOperator OperatorOver
  -- clockface
  setSourceRGB 0.78 0.22 0.11
  translate 0.5 0.5
  arc 0 0 (60/150) 0 (pi*2)
  fill
  -- clockface end
  restore

  save
  setSourceRGB 0 1 0
  selectFontFace "MxFont" FontSlantNormal FontWeightNormal
  setFontSize 0.2
  ext <- textExtents "Does this work?"
  moveTo (0.2) (0.2)
  showText "Does this work?"
  restore

  save
  setSourceRGB 0.3 0 0.8
  selectFontFace "MS PMincho" FontSlantNormal FontWeightNormal
  setFontSize 0.13
  ext <- textExtents "私は誰ですか。それとも何処か。"
  moveTo (0.2) (0.3)
  showText "私は誰ですか。それとも何処か。"
  restore

  -- translate 0.5 0.5
  -- scale 0.4 0.4
  -- setSourceRGB 0.16 0.18 0.19
  -- setLineWidth (1.5/60)
  -- setLineCap LineCapRound
  -- setLineJoin LineJoinRound
  -- drawHourMarks

  restore

drawClockBackground :: GTK.IsWidget widget => widget -> Bool -> Render ()
drawClockBackground canvas quality = do

  width  <- liftIO $ GTK.widgetGetAllocatedWidth  canvas
  height <- liftIO $ GTK.widgetGetAllocatedHeight canvas
  save
  scale (fromIntegral width) (fromIntegral height)

  save
  setOperator OperatorOver
  when quality drawDropShadow
  drawClockFace quality
  restore

  translate 0.5 0.5
  scale 0.4 0.4
  setSourceRGB 0.16 0.18 0.19
  setLineWidth (1.5/60)
  setLineCap LineCapRound
  setLineJoin LineJoinRound
  drawHourMarks

  restore

drawClockHands :: GTK.IsWidget widget => widget -> Bool -> Render ()
drawClockHands canvas quality = do

  width  <- liftIO $ GTK.widgetGetAllocatedWidth  canvas
  height <- liftIO $ GTK.widgetGetAllocatedHeight canvas
  save
  scale (fromIntegral width) (fromIntegral height)

  translate 0.5 0.5
  scale 0.4 0.4
  setSourceRGB 0.16 0.18 0.19
  setLineWidth (1.5/60)
  setLineCap LineCapRound
  setLineJoin LineJoinRound

  time <- liftIO (localTimeOfDay . zonedTimeToLocalTime <$> getZonedTime)
  let hours   = fromIntegral (todHour time `mod` 12)
      minutes = fromIntegral (todMin time)
      seconds = realToFrac (todSec time)

  drawHourHand quality hours minutes seconds
  drawMinuteHand quality minutes seconds
  drawSecondHand quality seconds

  restore

drawClockForeground :: Bool -> Int -> Int -> Render ()
drawClockForeground quality width height = do
  scale (fromIntegral width) (fromIntegral height)

  save
  translate 0.5 0.5
  scale 0.4 0.4
  setSourceRGB 0.16 0.18 0.19
  setLineWidth (1.5/60)
  setLineCap LineCapRound
  setLineJoin LineJoinRound

  when quality drawInnerShadow
  when quality drawReflection
  drawFrame quality
  restore

drawDropShadow =
  withRadialPattern 0.55 0.55 0.25 0.5 0.5 0.525 $ \p -> do
    patternAddColorStopRGBA p 0    0     0     0     0.811
    patternAddColorStopRGBA p 0.64 0.345 0.345 0.345 0.317
    patternAddColorStopRGBA p 0.84 0.713 0.713 0.713 0.137
    patternAddColorStopRGBA p 1    1     1     1     0
    patternSetFilter p FilterFast
    setSource p
    arc 0.5 0.5 (142/150) 0 (pi*2)
    fill

drawClockFace True =
  withLinearPattern 0.5 0 0.5 1 $ \p -> do
    patternAddColorStopRGB p 0 0.91 0.96 0.93
    patternAddColorStopRGB p 1 0.65 0.68 0.68
    patternSetFilter p FilterFast
    setSource p
    translate 0.5 0.5
    arc 0 0 (60/150) 0 (pi*2)
    fill
drawClockFace False = do
  setSourceRGB 0.78 0.82 0.805
  translate 0.5 0.5
  arc 0 0 (60/150) 0 (pi*2)
  fill

drawHourMarks = do
  save
  forM_ [1..12] $ \_ -> do
    rotate (pi/6)
    moveTo (4.5/6) 0
    lineTo (5.0/6) 0
  stroke
  restore

forM_ = flip mapM_

drawHourHand quality hours minutes seconds = do
  save
  rotate (-pi/2)
  setLineCap LineCapSquare
  setLineJoin LineJoinMiter
  rotate ( (pi/6) * hours
         + (pi/360) * minutes
         + (pi/21600) * seconds)

  -- hour hand's shadow
  when quality $ do
    setLineWidth (1.75/60)
    setOperator OperatorAtop
    setSourceRGBA 0.16 0.18 0.19 0.125
    moveTo (-2/15 + 0.025) 0.025
    lineTo (7/15 + 0.025) 0.025
    stroke

  -- the hand itself
  setLineWidth (1/60)
  setOperator OperatorOver
  setSourceRGB 0.16 0.18 0.19
  moveTo (-2/15) 0
  lineTo (7/15) 0
  stroke
  restore

drawMinuteHand quality minutes seconds = do
  save
  rotate (-pi/2)
  setLineCap LineCapSquare
  setLineJoin LineJoinMiter
  rotate ( (pi/30) * minutes
         + (pi/1800) * seconds)

  -- minute hand's shadow
  when quality $ do
    setLineWidth (1.75/60)
    setOperator OperatorAtop
    setSourceRGBA 0.16 0.18 0.19 0.125
    moveTo (-16/75 - 0.025) (-0.025)
    lineTo (2/3 - 0.025)    (-0.025)
    stroke

  -- the minute hand itself
  setLineWidth (1/60)
  setOperator OperatorOver
  setSourceRGB 0.16 0.18 0.19
  moveTo (-16/75) 0
  lineTo (2/3) 0
  stroke
  restore

drawSecondHand quality seconds = do
  save
  rotate (-pi/2)
  setLineCap LineCapSquare
  setLineJoin LineJoinMiter
  rotate (seconds * pi/30);

  -- shadow of second hand-part
  when quality $ do
    setOperator  OperatorAtop
    setSourceRGBA 0.16 0.18 0.19 0.125
    setLineWidth  (1.3125 / 60)
    moveTo (-1.5/5 + 0.025) 0.025
    lineTo (3/5 + 0.025) 0.025
    stroke

  -- second hand
  setOperator OperatorOver
  setSourceRGB 0.39 0.58 0.77
  setLineWidth (0.75/60)
  moveTo (-1.5/5) 0
  lineTo (3/5) 0
  stroke

  arc 0 0 (1/20) 0 (pi*2)
  fill
  arc (63/100) 0 (1/35) 0 (pi*2)
  stroke
  setLineWidth  (1/100)
  moveTo  (10/15) 0
  lineTo  (12/15) 0
  stroke
  setSourceRGB  0.31 0.31 0.31
  arc  0 0 (1/25) 0 (pi*2)
  fill
  restore

drawInnerShadow = do
  save
  setOperator OperatorOver
  arc 0 0 (142/150) 0 (pi*2)
  clip
  withRadialPattern 0.3 0.3 0.1 0 0 0.95 $ \p -> do
    patternAddColorStopRGBA p 0    1     1     1     0
    patternAddColorStopRGBA p 0.64 0.713 0.713 0.713 0.137
    patternAddColorStopRGBA p 0.84 0.345 0.345 0.345 0.317
    patternAddColorStopRGBA p 1    0     0     0     0.811
    patternSetFilter p FilterFast
    setSource p
    arc 0 0 (142/150) 0 (pi*2)
    fill
  restore

drawReflection = do
  save
  arc 0 0 (142/150) 0 (pi*2)
  clip
  rotate (-75 * pi/180)
  setSourceRGBA 0.87 0.9 0.95 0.25
  moveTo (-1) (-1)
  lineTo 1 (-1)
  lineTo 1 1
  curveTo 1 0.15 (-0.15) (-1) (-1) (-1)
  fill
  moveTo (-1) (-1)
  lineTo (-1) 1
  lineTo 1 1
  curveTo (-0.5) 1 (-1) 0.5 (-1) (-1)
  fill
  restore

drawFrame True = do
  save
  withRadialPattern (-0.1) (-0.1) 0.8 0 0 1.5 $ \p -> do
    patternAddColorStopRGB p 0   0.4  0.4  0.4
    patternAddColorStopRGB p 0.2 0.95 0.95 0.95
    patternSetFilter p FilterFast
    setSource p
    setLineWidth (10/75)
    arc 0 0 (142/150) 0 (pi*2)
    stroke

  withRadialPattern (-0.1) (-0.1) 0.8 0 0 1.5 $ \p -> do
    patternAddColorStopRGB p 0   0.9  0.9  0.9
    patternAddColorStopRGB p 0.2 0.35 0.35 0.35
    patternSetFilter p FilterFast
    setSource p
    setLineWidth (10/75)
    arc 0 0 (150/150) 0 (pi*2)
    stroke
  restore
drawFrame False = do
  save
  setSourceRGB 0 0 0
  setLineWidth (10/75)
  arc 0 0 1 0 (pi*2)
  stroke
  restore

initialSize :: Int
initialSize = 256

drawCanvasHandler :: GTK.IsWidget widget => widget -> Render Bool
drawCanvasHandler widget =  
  do -- drawClockBackground widget True
     -- drawClockHands widget True 
     drawMyLine widget
     return True

main :: (forall widget. GTK.IsWidget widget => widget -> Render Bool)
     -> (Text -> IO ())
     -> IO ()
main renderer keyhandler = do
  GTK.init
  window <- GTK.windowNew

  return ()

  -- GTK.windowSetPosition window GTK.WindowPositionCenterAlways

  -- GTK.widgetSetAppPaintable window True

  GTK.windowSetDefaultSize window (fromIntegral initialSize)
                                  (fromIntegral initialSize)

  {-
  geometry <- GDK.newZeroGeometry
  GDK.setGeometryMaxWidth  geometry 512
  GDK.setGeometryMaxHeight geometry 512
  GDK.setGeometryMinWidth  geometry 32
  GDK.setGeometryMinHeight geometry 32
  GDK.setGeometryMinAspect geometry 1
  GDK.setGeometryMaxAspect geometry 1

  GTK.windowSetGeometryHints window (Just window) (Just geometry) []

  GTK.onWidgetKeyPressEvent window $ \keyPressInfo -> do
    keyVal <- GDK.getEventKeyKeyval keyPressInfo
    keyName <- fromMaybe Text.empty <$> GDK.keyvalName keyVal
    case Text.unpack keyName of
      "Escape" -> do GTK.mainQuit
                     return True
      _        -> keyhandler keyName >> GTK.widgetQueueDraw window >> return True
        -- return False

  GTK.onWidgetButtonPressEvent window $ \button -> do
    btnNo <- GDK.getEventButtonButton button
    x     <- GDK.getEventButtonX button
    y     <- GDK.getEventButtonY button
    time  <- GDK.getEventButtonTime button
    case btnNo of
      1  -> do GTK.windowBeginMoveDrag window 1 (round x) (round y) time  -- left button
               return True
      2  -> do GTK.windowBeginResizeDrag window GDK.WindowEdgeSouthEast 2 -- middle button
                                         (round x) (round y) time
               return True
      _  -> return False

  canvas <- GTK.drawingAreaNew
  GTK.containerAdd window canvas

  --------
  -- get my surface
  -- gdkwindow <- (castTo GDK.Window window)
  --
  -- on this surface I want to do my drawing operations, and then only "copy"
  -- them to the given surface in `onDraw`.
  -- Here I can do my custom computation of delta difference incurred by an input.
  --
  -- Since we create the surface using `createSimilarSurface`, it should be faster.
  -- See https://news.ycombinator.com/item?id=16539446
  --
  -- gdkwindow <- GTK.widgetGetWindow canvas
  -- case gdkwindow of
  --   Nothing -> error ""
  --   Just gdkwindow -> do
  --     mygoodsurface <- GDK.windowCreateSimilarSurface gdkwindow GI.Cairo.ContentColorAlpha 400 400
  --     renderWith (Surface mygoodsurface) undefined
  --     undefined
  --      -- mygoodsurface
  --     -- renderWith (Surface mygoodsurface) undefined
  --     return ()
  --
  --------


  GTK.setWindowDecorated window True
  GTK.setWindowResizable window True
  GTK.setWindowTitle window (pack "Hata Editor")

  GTK.onWidgetDraw canvas $ renderWithContext (renderer canvas) -- (drawCanvasHandler canvas)

  GTK.widgetShowAll window
  timeoutAdd GI.GLib.PRIORITY_DEFAULT 1000 (GTK.widgetQueueDraw window >> return True)
  GTK.main

-}

