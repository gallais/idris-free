module Main

import Test.Golden

%default covering

------------------------------------------------------------------------
-- Test cases

freeTests : TestPool
freeTests = MkTestPool "Free constructions" [] Nothing
  [ "monad001"
  , "alternative001"
  , "alternative002"
  , "commit001"
  ]

main : IO ()
main = runner
  [ testPaths "free" freeTests
  ] where

    testPaths : String -> TestPool -> TestPool
    testPaths dir = { testCases $= map ((dir ++ "/") ++) }
