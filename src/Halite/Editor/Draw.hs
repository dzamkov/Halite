{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Halite.Editor.Draw where

import qualified System.Console.ANSI as ANSI
import qualified System.Console.Terminal.Size as Size
import Data.Monoid
import Control.Monad.State

-- | A horizontal length in the terminal.
type Width = Int

-- | A vertical length in the terminal.
type Height = Int

-- | A horizontal offset in the terminal.
type X = Int

-- | A vertical offset in the terminal.
type Y = Int

-- | Light blue color.
lightBlue :: Color
lightBlue = (ANSI.Vivid, ANSI.Blue)

-- | White color.
white :: Color
white = (ANSI.Vivid, ANSI.White)

-- | Light gray color.
lightGray :: Color
lightGray = (ANSI.Dull, ANSI.White)

-- | Black color.
black :: Color
black = (ANSI.Dull, ANSI.Black)

-- | A terminal color.
type Color = (ANSI.ColorIntensity, ANSI.Color)

-- | Combines a background 'Color' with a foreground 'Color'.
type Appearance = (Color, Color)

-- | Describes the state of a terminal cursor.
data DrawState = DrawState {

    -- | The absolute position of the cursor.
    pos :: (X, Y),

    -- | The appearance for future draw operations.
    appr :: Appearance,

    -- | Indicates whether the cursor is visible.
    visible :: Bool,

    -- | The size of the terminal.
    termSize :: (Width, Height) }
    deriving (Eq, Ord, Show)

-- | Synchronizes the current 'DrawState' with the actual state of the
-- terminal, possibly by altering the terminal.
sync :: StateT DrawState IO ()
sync = do
    let pos@(x, y) = (0, 0)
        appr@((nBI, nBC), (nFI, nFC)) = (black, lightGray)
    liftIO ANSI.clearScreen
    liftIO $ ANSI.setCursorPosition x y
    liftIO $ ANSI.setSGR [
        ANSI.SetColor ANSI.Background nBI nBC,
        ANSI.SetColor ANSI.Foreground nFI nFC]
    Just win <- liftIO Size.size
    put DrawState {
        pos = pos,
        appr = appr,
        visible = True,
        termSize = (Size.width win, Size.height win) }

-- | Sets the position of the cursor.
changePos :: (X, Y) -> StateT DrawState IO ()
changePos nPos@(nX, nY) = do
    st <- get
    let oPos = pos st
    when (oPos /= nPos) $ do
        liftIO $ ANSI.setCursorPosition nX nY
        put $ st { pos = nPos }

-- | Sets the background for future draw operations.
changeBack :: Color -> StateT DrawState IO ()
changeBack nBack@(nI, nC) = do
    st <- get
    let (oBack, oFore) = appr st
    when (oBack /= nBack) $ do
        liftIO $ ANSI.setSGR [ANSI.SetColor ANSI.Background nI nC]
        put $ st { appr = (nBack, oFore) }

-- | Sets the foreground for future draw operations.
changeFore :: Color -> StateT DrawState IO ()
changeFore nFore@(nI, nC) = do
    st <- get
    let (oBack, oFore) = appr st
    when (oFore /= nFore) $ do
        liftIO $ ANSI.setSGR [ANSI.SetColor ANSI.Foreground nI nC]
        put $ st { appr = (oBack, nFore) }

-- | Sets the appearance for future draw operations.
changeAppr :: Appearance -> StateT DrawState IO ()
changeAppr nAppr@((nBI, nBC), (nFI, nFC)) = do
    st <- get
    let oAppr = appr st
    when (oAppr /= nAppr) $ do
        liftIO $ ANSI.setSGR [
            ANSI.SetColor ANSI.Background nBI nBC,
            ANSI.SetColor ANSI.Foreground nFI nFC]
        put $ st { appr = nAppr }

-- | A primitive draw operation that requires only one modification to
-- the current 'DrawState'.
data DrawOp
    = DrawStr Appearance (X, Y) String
    | DrawSpace Color (X, Y) Width
    deriving (Eq, Ord, Show)

-- | Applies a primitive draw operation to the current terminal.
runDrawOp :: DrawOp -> StateT DrawState IO ()
runDrawOp op = res where
    draw (x, y) width setup inner = do
        changePos (x, y)
        setup
        liftIO inner
        st <- get
        let tWidth = fst $ termSize st
            nX = (x + width) `rem` tWidth
            nY = y + ((x + width) `div` tWidth)
        put $ st { pos = (nX, nY) }
    res = case op of
        DrawStr appr pos str -> draw pos (length str)
            (changeAppr appr) (putStr str)
        DrawSpace back pos width -> draw pos width
            (changeBack back) (putStr $ replicate width ' ')

-- | A draw operation that can be applied to a terminal.
newtype Draw = Draw [DrawOp] deriving (Eq, Ord, Show, Monoid)

-- | Applies a draw operation to the current terminal.
runDraw :: Draw -> StateT DrawState IO ()
runDraw (Draw ops) = forM_ ops runDrawOp

-- | Constructs a draw operation for a string.
string :: Appearance -> (X, Y) -> String -> Draw
string appr pos str = Draw [DrawStr appr pos str]

-- | Constructs a draw operation for a space.
space :: Color -> (X, Y) -> Width -> Draw
space col pos width = Draw [DrawSpace col pos width]
