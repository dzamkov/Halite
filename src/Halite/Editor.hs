{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Halite.Editor where

import Halite.Expression
import Halite.Editor.Input
import Halite.Editor.Draw (sync, runDraw)
import Halite.Editor.Display
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
    let ctx = Context {
            name = id,
            pos = (0, 0),
            ctxOut = Nothing,
            ctxLeft = Nothing,
            ctxRight = Nothing }
        exp = Exp (Var "hello")
        cursor = display exp ctx
    flip evalStateT undefined $ do
        sync
        let win cursor = do
                runDraw (highlight cursor)
                command <- liftIO getCommand
                let navigate f = do
                        runDraw (unhighlight cursor)
                        win (f cursor)
                case command of
                    Navigate NLeft -> navigate navLeft
                    Navigate NRight -> navigate navRight
                    Navigate NIn -> navigate navInLeft
                    Navigate NOut -> navigate navOut
                    Quit -> return ()
        win cursor
