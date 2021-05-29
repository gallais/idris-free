module Monad

import Free.Common
import Free.Monad
import Free.Examples

import Data.List

test : IO ()
test = run cat3
