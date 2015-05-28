import Halite.Editor.Input
import qualified System.Console.ANSI as ANSI
import Control.Monad.State
import qualified Data.List as List

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

-- | A primitive editable unit with its independent meaning.
data Atom
    = Hole
    | Word String

-- | An application tree of 'Atom's.
data Phrase = Phrase Atom [Phrase]

-- | Describes the context surronding a phrase.
data PhraseContext
    = CPhraseRoot
    | CPhraseWithin Atom [Phrase] [Phrase] PhraseContext

-- | A zipper for a phrase, which can target an atom or a sub-phrase.
data PhraseZipper
    = ZPhraseHead Atom [Phrase] PhraseContext
    | ZPhrase Atom Phrase [Phrase] PhraseContext

-- | Constructs a zipper for a phrase with the given context.
phraseZipper :: PhraseContext -> Phrase -> PhraseZipper
phraseZipper c (Phrase h []) = ZPhraseHead h [] c
phraseZipper c (Phrase h (t : r)) = ZPhrase h t r c

-- | Describes an edit buffer from the perspective of the user cursor.
data Window
    = Over PhraseZipper
    | Writing String [Phrase] PhraseContext

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
        'j' -> return $ Navigate NOut
        'k' -> return $ Navigate NIn
        'l' -> return $ Navigate NRight
        'q' -> return Quit
        _ -> getCommand

-- | Sets the background color.
setBack :: Color -> IO ()
setBack (i, c) = ANSI.setSGR [ANSI.SetColor ANSI.Background i c]

-- | Sets the foreground color.
setFore :: Color -> IO ()
setFore (i, c) = ANSI.setSGR [ANSI.SetColor ANSI.Foreground i c]

-- | Uses the given drawing procedure to draw an object normally.
drawNormal :: (Bool -> IO ()) -> IO ()
drawNormal x = x True

-- | Uses the given drawing procedure to draw a highlighted object.
drawHighlight :: (Bool -> IO ()) -> IO ()
drawHighlight x = do
    setBack (ANSI.Vivid, ANSI.Blue)
    setFore (ANSI.Vivid, ANSI.White)
    x False

-- | Determines the draw width of an 'Atom', and prepares a procedure to
-- draw it.
drawAtom :: Atom -> (Width, Bool -> IO ())
drawAtom Hole = (1, \color -> do
    when color $ setFore (ANSI.Vivid, ANSI.Cyan)
    putStr "_")
drawAtom (Word str) = (length str, \color -> do
    when color $ setFore (ANSI.Dull, ANSI.White)
    putStr str)

-- | Determines the draw width of a list of 'Phrase's, each prefixed with
-- a space, and prepares a procedure to draw it.
drawItems :: [Phrase] -> (Width, Bool -> IO ())
drawItems = List.foldl' (\(w, d) item ->
    let (iWidth, iDraw) = drawPhrase item
    in (w + 1 + iWidth, \color -> do
        d color
        putStr " "
        iDraw color))
    (0, const $ return ())

-- | Determines the draw width of a 'Phrase', and prepares a procedure to
-- draw it.
drawPhrase :: Phrase -> (Width, Bool -> IO ())
drawPhrase (Phrase atom []) = drawAtom atom
drawPhrase (Phrase head tail) =
    let (hWidth, hDraw) = drawAtom head
        (tWidth, tDraw) = drawItems tail
    in (1 + hWidth + tWidth + 1, \color -> do
        when color $ setFore (ANSI.Vivid, ANSI.White)
        putStr "("
        hDraw color
        tDraw color
        when color $ setFore (ANSI.Vivid, ANSI.White)
        putStr ")")

-- | Processes a navigate command on an 'Over' state, and performs the
-- corresponding drawing operations.
navigate :: Navigation -> PhraseZipper -> IO PhraseZipper
navigate NLeft st@(ZPhraseHead _ _ CPhraseRoot) = return st
navigate NLeft st@(ZPhrase _ _ _ CPhraseRoot) = return st
navigate NRight (ZPhraseHead h (t : r) c) = do
    setBack (ANSI.Dull, ANSI.Black)
    let (_, hD) = drawAtom h
    hD True
    putStr " "
    let (tW, tD) = drawPhrase t
    setBack (ANSI.Vivid, ANSI.Blue)
    setFore (ANSI.Vivid, ANSI.White)
    tD False
    ANSI.cursorBackward tW
    return (phraseZipper (CPhraseWithin h [] r c) t)
navigate NRight st@(ZPhrase _ _ _ CPhraseRoot) = return st
navigate NIn st@(ZPhraseHead _ _ _) = return st
navigate NIn (ZPhrase h t r c) = do
    setBack (ANSI.Dull, ANSI.Black)
    setFore (ANSI.Vivid, ANSI.White)
    putStr "("
    let (hW, _) = drawAtom h
    ANSI.cursorForward hW
    let (tW, tD) = drawItems (t : r)
    tD True
    putStr ")"
    ANSI.cursorBackward (hW + tW + 1)
    return (ZPhraseHead h (t : r) c)

main :: IO ()
main = do
    let pHead = Word "test"
        p2 = Phrase Hole []
        p3 = Phrase (Word "x") [Phrase (Word "y") [], Phrase (Word "z") []]
        phrase = Phrase pHead [p2, p3]
        (pWidth, pDraw) = drawPhrase phrase
    drawHighlight pDraw
    ANSI.cursorBackward pWidth
    let win = Over $ ZPhrase pHead p2 [p3] CPhraseRoot
        loop (Over zipper) = do
            command <- getCommand
            case command of
                Navigate nav -> do
                    nZipper <- navigate nav zipper
                    loop (Over nZipper)
                Quit -> return ()
        loop (Writing _ _ _) = undefined -- TODO
    loop win
