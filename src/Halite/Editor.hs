{-# LANGUAGE ImplicitParams #-}
module Halite.Editor where

import Halite.Expression
import Halite.Editor.Expression
import Halite.Editor.Input
import Halite.Editor.Draw (sync, runDraw)
import qualified Halite.Editor.Display as Display
import Halite.Editor.Control (AnyControl (..))
import qualified Halite.Editor.Control as Control
import Control.Monad.State

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

main :: IO ()
main = do
    let ?style = Display.defaultStyle
    let exp = Exp (Var "hello")
        lookup = Atom
        shape = Display.Inline 80
        control = build exp shape lookup
    case control of
        AnyControl control -> flip evalStateT undefined $ do
            sync
            runDraw $ Control.draw control False
