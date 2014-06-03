module Halisp.Draw (
	Width,
	Height,
	InlineFigure,
	Figure,
	variableColor,
	symbolColor,
	operatorColor,
	lineColor,
	text,
	(+$),
	DTerm,
	term,
	block,
	pad,
	border,
	(|||),
	(===),
	drawInline,
	drawLine,
	draw
) where

import qualified System.Console.ANSI as Terminal
import Halisp.Term

-- Identifies a width (in characters) for a console.
type Width = Int

-- Identifies a height (in characters) for a console.
type Height = Int

-- A static in-line figure that can be drawn to the console.
data InlineFigure = InlineFigure Width (IO ())

-- A static figure that can be drawn to the console.
data Figure = Figure Width Height (Width -> Height -> IO ())

-- A color that can be used on a console.
data Color = Color Terminal.Color Terminal.ColorIntensity

-- The color used to draw variable names.
variableColor = Color Terminal.Green Terminal.Vivid

-- The color used to draw symbol names.
symbolColor = Color Terminal.Green Terminal.Dull

-- The color used to draw operators.
operatorColor = Color Terminal.Cyan Terminal.Dull

-- The color used to draw lines.
lineColor = Color Terminal.White Terminal.Dull

-- Sets the current color for the terminal.
setColor :: Color -> IO ()
setColor (Color c i) = Terminal.setSGR [Terminal.SetColor Terminal.Foreground i c]

-- Constructs a figure for inline text.
text :: Color -> String -> InlineFigure
text color str = InlineFigure (length str) $ (setColor color >> putStr str)
	
-- Concatenates two inline figures.
(+$) :: InlineFigure -> InlineFigure -> InlineFigure
(+$) (InlineFigure xw xd) (InlineFigure yw yd) = InlineFigure (xw + yw) (xd >> yd)

-- A term that can be drawn.
type DTerm = APTerm String String

-- Constructs a figure for a term.
term :: DTerm -> InlineFigure
term (Term (Var x)) = text variableColor x
term (Term (Value (App sym args))) = res where
	op str = text operatorColor str
	symFig = text symbolColor sym
	innerArgsFig = foldl (\f a -> f +$ op ", " +$ term a) (term (head args)) (tail args)
	argsFig = op "[" +$ innerArgsFig +$ op "]"
	res = if null args then symFig else symFig +$ argsFig

-- Combines a list of inline figures into a single block figure.
block :: [InlineFigure] -> Figure
block items = res where
	width = maximum $ map (\(InlineFigure w _) -> w) items
	height = length items
	drawFirst = (\(InlineFigure w d) -> d >> Terminal.cursorBackward w) (head items)
	drawCombine accum (InlineFigure w d) = (accum >> Terminal.cursorDown 1 >>
		d >> Terminal.cursorBackward w)
	draw w h = do
		foldl drawCombine drawFirst (tail items)
		Terminal.cursorForward w
		Terminal.cursorDown (h - height)
	res = Figure width height draw
	
-- Applies padding to a figure. The padding amounts are given in the following order:
-- left, top, right, bottom.
pad :: Int -> Int -> Int -> Int -> Figure -> Figure
pad l t r b (Figure iw ih id) = res where
	width = l + iw + r
	height = t + ih + b
	draw w h = do
		Terminal.cursorForward l
		Terminal.cursorDown t
		id (w - l - r) (h - t - b)
		Terminal.cursorForward r
		Terminal.cursorDown b
	res = Figure width height draw

-- Draws a horizontal line of the given length.
hline :: Int -> IO ()
hline 0 = return ()
hline n = do
	putStr "-"
	hline (n - 1)
	
-- Draws a vertical line of the given length, leaving the cursor forward of the last cell
-- of the line.
vline :: Int -> IO ()
vline n = do
	putStr "|"
	if n > 1 then do
		Terminal.cursorBackward 1
		Terminal.cursorDown 1
		vline (n - 1)
	else return ()
	
-- Applies a border to a figure.
border :: Color -> Figure -> Figure
border color (Figure iw ih id) = res where
	width = 1 + iw + 1
	height = 1 + ih + 1
	draw w h = do
		setColor color
		putStr "+"
		hline (w - 2)
		putStr "+"
		Terminal.cursorBackward 1
		Terminal.cursorDown 1
		vline (h - 2)
		Terminal.cursorBackward w
		Terminal.cursorDown 1
		putStr "+"
		hline (w - 2)
		putStr "+"
		Terminal.cursorBackward w
		Terminal.cursorUp (h - 2)
		vline (h - 2)
		Terminal.cursorUp (h - 3)
		id (w - 2) (h - 2)
		Terminal.cursorForward 1
		Terminal.cursorDown 1
	res = Figure width height draw

-- Constructs a figure by placing the two given figures side-by-side, with a vertical line
-- seperating them.
(|||) :: Figure -> Figure -> Figure	
(|||) (Figure lw lh ld) (Figure rw rh rd) = res where
	width = lw + 1 + rw
	height = max lh rh
	draw w h = do
		let fw = w * lw `div` (lw + rw)
		let sw = w - fw - 1
		ld fw h
		Terminal.cursorUp (h - 1)
		setColor lineColor
		vline h
		Terminal.cursorUp (h - 1)
		rd sw h
	res = Figure width height draw

-- Constructs a figure by placing the two given figures atop each other, with a horizontal
-- line seperating them.
(===) :: Figure -> Figure -> Figure	
(===) (Figure tw th td) (Figure bw bh bd) = res where
	width = max tw bw
	height = th + 1 + bh
	draw w h = do
		let fh = h * th `div` (th + bh)
		let sh = h - fh - 1
		td w fh
		Terminal.cursorBackward w
		Terminal.cursorDown 1
		setColor lineColor
		hline w
		Terminal.cursorBackward w
		Terminal.cursorDown 1
		bd w sh
	res = Figure width height draw

-- Draws an inline figure to the console.
drawInline :: InlineFigure -> IO ()
drawInline (InlineFigure _ d) = d >> Terminal.setSGR [Terminal.Reset]

-- Draws an inline figure to the console, on its own line.
drawLine :: InlineFigure -> IO ()
drawLine (InlineFigure _ d) = d >> Terminal.setSGR [Terminal.Reset] >> putStrLn ""
		
-- Draws a figure to the console.
draw :: Figure -> IO ()
draw (Figure w h d) = do
	foldl (>>) (return ()) $ replicate h (putStrLn "")
	Terminal.cursorUp h
	d w h 
	Terminal.setSGR [Terminal.Reset]
	putStrLn ""