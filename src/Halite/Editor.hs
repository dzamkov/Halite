{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Halite.Editor where

import Halite.Editor.Input
import qualified System.Console.ANSI as ANSI
import Control.Monad.State
import Data.Monoid
import Control.Applicative

-- | A horizontal length in the terminal.
type Width = Int

-- | A vertical length in the terminal.
type Height = Int

-- | A horizontal offset in the terminal.
type X = Int

-- | A vertical offset in the terminal.
type Y = Int

-- | A terminal color.
type Color = (ANSI.ColorIntensity, ANSI.Color)

-- | Sets the background color.
setBack :: Color -> IO ()
setBack (i, c) = ANSI.setSGR [ANSI.SetColor ANSI.Background i c]

-- | Sets the foreground color.
setFore :: Color -> IO ()
setFore (i, c) = ANSI.setSGR [ANSI.SetColor ANSI.Foreground i c]

-- | Describes a single-line colored string that can be displayed in the
-- terminal.
newtype Inline = Inline [(Color, String)] deriving (Monoid)

-- | Constructs an 'Inline' for a string of uniform color.
inlineUniform :: Color -> String -> Inline
inlineUniform col str = Inline [(col, str)]

-- | Constructs an 'Inline' for a space of the given length.
inlineSpace :: Width -> Inline
inlineSpace width = Inline [((ANSI.Dull, ANSI.Black), replicate width ' ')]

-- | Determines the display width of an 'Inline'.
inlineWidth :: Inline -> Width
inlineWidth (Inline parts) = sum $ map (length . snd) parts

-- | Draws an 'Inline' to the current cursor position.
drawInline :: Inline -> IO ()
drawInline (Inline parts) = do
    setBack (ANSI.Dull, ANSI.Black)
    forM_ parts $ \(color, str) -> do
        setFore color
        putStr str

-- | Draws an 'Inline' to the current cursor position using a
-- highlighted style.
drawInlineHighlight :: Inline -> IO ()
drawInlineHighlight (Inline parts) = do
    setBack (ANSI.Vivid, ANSI.Blue)
    setFore (ANSI.Vivid, ANSI.White)
    forM_ parts $ \(_, str) -> putStr str

-- | An expression that can be edited by the user. Note that this type
-- may include display information in addition to the logical structure of
-- the expression.
data Expression
    = Hole
    | Word String
    | App [Expression]

-- | Describes the context surronding an expression.
data ExpressionContext
    = Root
    | WithinApp [Expression] [Expression] ExpressionContext

-- | Constructs an 'Inline' to display an expression.
inlineExpression :: Expression -> Inline
inlineExpression Hole = inlineUniform (ANSI.Vivid, ANSI.White) "_"
inlineExpression (Word str) = inlineUniform (ANSI.Dull, ANSI.White) str
inlineExpression (App []) = inlineUniform (ANSI.Vivid, ANSI.White) "()"
inlineExpression (App (h : t)) =
    inlineUniform (ANSI.Vivid, ANSI.White) "(" <>
    inlineExpression h <>
    mconcat (map (\e -> inlineSpace 1 <> inlineExpression e) t) <>
    inlineUniform (ANSI.Vivid, ANSI.White) ")"

-- | Describes an edit buffer from the perspective of the user's cursor.
-- This should include enough information to extract the logical expression for
-- the buffer, the currently displayed contents of the window, and the
-- edit context the user is in.
data Window
    = Over Expression ExpressionContext
    | Writing String ExpressionContext

-- | Describes a navigation command.
data Navigation
    = NLeft
    | NRight
    | NIn
    | NOut

-- | Describes an edit command.
data Command
    = Navigate Navigation
    | Quit

-- | Waits for the user to type a comand.
getCommand :: IO Command
getCommand = do
    ch <- getHiddenChar
    case ch of
        'h' -> return $ Navigate NLeft
        'j' -> return $ Navigate NRight
        'k' -> return $ Navigate NIn
        'l' -> return $ Navigate NOut
        'q' -> return Quit
        _ -> getCommand

-- | Processes a navigate command on an 'Over' state, and performs the
-- corresponding drawing operations.
navigate :: Navigation
    -> (Expression, ExpressionContext)
    -> IO (Expression, ExpressionContext)
navigate NLeft st@(e, cxt) = res where
    goLeft _ Root = Nothing
    goLeft e (WithinApp (n : l) r cxt) =
        let nInline = inlineExpression n
        in Just (nInline, 1, n, WithinApp l (e : r) cxt)
    goLeft e (WithinApp [] r cxt) =
        (\(i, w, e, c) -> (i, w + 1, e, c)) <$> goLeft (App (e : r)) cxt
    res = case goLeft e cxt of
        Nothing -> return st
        Just (nInline, w, n, nCxt) -> do
            let eInline = inlineExpression e
            drawInline eInline
            ANSI.cursorBackward (inlineWidth nInline + w + inlineWidth eInline)
            drawInlineHighlight nInline
            ANSI.cursorBackward (inlineWidth nInline)
            return (n, nCxt)
navigate NRight st@(e, cxt) = res where
    goRight _ Root = Nothing
    goRight e (WithinApp l (n : r) cxt) =
        let nInline = inlineExpression n
        in Just (nInline, 1, n, WithinApp (e : l) r cxt)
    goRight e (WithinApp l [] cxt) =
        (\(i, w, e, c) -> (i, w + 1, e, c)) <$> goRight (App (l ++ [e])) cxt
    res = case goRight e cxt of
        Nothing -> return st
        Just (nInline, w, n, nCxt) -> do
            let eInline = inlineExpression e
            drawInline eInline
            ANSI.cursorForward w
            drawInlineHighlight nInline
            ANSI.cursorBackward (inlineWidth nInline)
            return (n, nCxt)
navigate NIn st@(Hole, _) = return st
navigate NIn st@(Word _, _) = return st
navigate NIn st@(App [], _) = return st
navigate NIn (e@(App (h : t)), cxt) = do
    let eInline = inlineExpression e
        hInline = inlineExpression h
    drawInline eInline
    ANSI.cursorBackward (inlineWidth eInline - 1)
    drawInlineHighlight hInline
    ANSI.cursorBackward (inlineWidth hInline)
    return (h, WithinApp [] t cxt)
navigate NOut st@(_, Root) = return st
navigate NOut (e, WithinApp l r cxt) = do
    let f = App $ reverse l ++ [e] ++ r
        fInline = inlineExpression f
        bWidth = 1 + sum (map (\e -> 1 + inlineWidth (inlineExpression e)) l)
    ANSI.cursorBackward bWidth
    drawInlineHighlight fInline
    ANSI.cursorBackward (inlineWidth fInline)
    return (f, cxt)

main :: IO ()
main = do
    let test = App [Word "test", Hole, App [Word "x", Word "y", Word "z"]]
    drawInlineHighlight $ inlineExpression test
    ANSI.cursorBackward $ inlineWidth $ inlineExpression test
    let win = Over test Root
        loop (Over exp cxt) = do
            command <- getCommand
            case command of
                Navigate nav -> do
                    (nExp, nCxt) <- navigate nav (exp, cxt)
                    loop (Over nExp nCxt)
                Quit -> return ()
        loop (Writing _ _) = undefined -- TODO
    loop win
