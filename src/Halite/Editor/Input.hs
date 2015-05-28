{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
module Halite.Editor.Input (
    getHiddenChar,
) where

import qualified System.IO as IO
import Data.Char
import Foreign.C.Types

getHiddenChar :: IO Char
#ifdef mingw32_HOST_OS
getHiddenChar = fmap (chr.fromEnum) c_getch
foreign import ccall safe "conio.h _getch" c_getch :: IO CInt
#else
getHiddenChar = do
    IO.hSetEcho IO.stdin False
    IO.getChar
#endif
