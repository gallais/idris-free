module Main

import Test.Golden

%default covering

------------------------------------------------------------------------
-- Test cases

monadTests : TestPool
monadTests = MkTestPool "Free Monad" []
  [ "monad001"
  ]

alternativeTests : TestPool
alternativeTests = MkTestPool "Free Alternative" []
  [
  ]

commitTests : TestPool
commitTests = MkTestPool "Free Alternative with Commit" []
  [
  ]

main : IO ()
main = runner
  [ testPaths "monad" monadTests
  , testPaths "alternative" alternativeTests
  , testPaths "commit" commitTests
  ] where

    testPaths : String -> TestPool -> TestPool
    testPaths dir = record { testCases $= map ((dir ++ "/") ++) }
