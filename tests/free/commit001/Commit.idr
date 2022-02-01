module Commit

import Free.Common
import Free.Commit
import Free.Examples

import Data.List

test1 : IO ()
test1 = run cat3

test2 : IO ()
test2 = run $ do
  ignore $ echo 3
  ignore $ echo 2
  ignore $ echo 1
  putStrLn "boom"

test3 : IO ()
test3 = run $ sequence_ (replicate 3 nonEmpty)
   <|> error "Failed!"
   <|> putStrLn "Ouch: error in the error handler!"
   <|> putStrLn "This better not show up!"

test4 : IO ()
test4 = run $
  do n <- (error "Not here" <|> echo Z <|> echo (S Z))
     if n /= Z
       then putStrLn (show n)
       else error "No backtracking in the first bind"

test5 : IO ()
test5 = run $ sequence_ (replicate 3 (nonEmpty *> Commit))
   <|> error "Failed!"
   <|> putStrLn "Ouch: error in the error handler!"
   <|> putStrLn "This better not show up!"

-- Double commit
test6 : IO ()
test6 = run
  $ ((putStrLn "Failing..." *> Commit *> Commit *> putStrLn "Now!" *> fail) <|> putStrLn "bypassed")
    <|> putStrLn "And recovering!" -- success
    <|> putStrLn "unreachable"

-- Must
test7 : IO ()
test7 = run $ (<|> putStrLn "No gonnae do that") $
  do putStrLn "This."
     Must (fail <|> putStrLn "And that.")
     Must fail <|> putStrLn "unreachable"
