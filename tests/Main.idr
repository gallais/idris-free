module Main

import Test.Golden

%default covering

------------------------------------------------------------------------
-- Test cases

freeTests : TestPool
freeTests = MkTestPool "Free constructions" [] Nothing
  [ "alternative001"
  , "monad001"
  , "commit001"
  , "mixed001"
  ]

main : IO ()
main = runner
  [ testPaths "free" freeTests
  ] where

    testPaths : String -> TestPool -> TestPool
    testPaths dir = { testCases $= map ((dir ++ "/") ++) }
