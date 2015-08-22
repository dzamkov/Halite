{-# LANGUAGE ImplicitParams #-}
module Halite.Editor where

import Halite.Editor.Input
import Halite.Editor.Draw (sync, runDraw)
import qualified Halite.Editor.Draw as Draw
import Halite.Editor.Control
import Halite.Editor.Display
import Halite.Editor.Style
import Data.Monoid
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

display :: Display ()
display =
    let ?style = styleDefault
    in spaceList [
        atom "abcdefgh",
        atom "ijklmnopqrst",
        atom "uvwxyzabc",
        bracketr $ spaceList [
            atom "defghijk",
            atom "lmnopqrs",
            atom "tuvwxyzabc"],
        atom "defghijklmnop"] <> varSpace

main :: IO ()
main = do
    let inst : _ = instantiate display (Variable 50 50)
        appr = (Draw.black, Nothing)
        drawInst = draw inst appr
    flip evalStateT undefined $ do
        sync
        runDraw drawInst
