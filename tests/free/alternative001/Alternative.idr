module Alternative

import Free.Common
import Free.Alternative
import Free.Examples

import Data.List

test1 : IO ()
test1 = run cat3

test2 : IO ()
test2 = run countdown

test3 : IO ()
test3 = run getNonEmpty

test4 : IO ()
test4 = run noBacktracking
