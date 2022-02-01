module Monad

import Free.Common
import Free.Monad
import Free.Examples

import Data.List

test1 : IO ()
test1 = run cat3

test2 : IO ()
test2 = run countdown
