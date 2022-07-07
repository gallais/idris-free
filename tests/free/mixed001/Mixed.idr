import Free.Common
import Free.Examples

import Free.Mixed

%hide Prelude.putStrLn
%hide Examples.putStrLn
%hide Prelude.getLine

-- this is non-blocking so make it unguarded
putStrLn : String -> Free (const Eff) False ()
putStrLn str = lift (PutStrLn str)

-- this is blocking so make it guarded
getLine : Free (const Eff) True String
getLine = lift Get

until : (empty : Bool) -> Free (const Eff) True ()
until empty = Mixed.do
  x <- getLine
  ifThenElse empty
    (ifThenElse (x == "") (putStrLn "Found an empty line")
      $ forget $ do
        putStrLn #"Oops, "\#{x}" is not empty"#
        until empty)
    (ifThenElse (x /= "") (putStrLn #"Found a non-empty line: "\#{x}""#)
      $ forget $ do
        putStrLn #"Oops, found an empty line"#
        until empty)

test : IO ()
test = do
  run {g = True} (until True)
  run {g = True} (until False)
