module Monad

import Free.Common
import Free.Monad

import Data.List

export
prog : Free Eff ()
prog = sequence_ (replicate 3 printInput) where

  printInput : Free Eff ()
  printInput = do
    n <- lift Get
    lift (PutStrLn (show n))

test : IO ()
test = run prog
