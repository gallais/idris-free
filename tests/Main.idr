module Main

import Test.Golden

%default covering

------------------------------------------------------------------------
-- Test cases

monadTests : TestPool
monadTests = MkTestPool "Free Monad" [] Nothing
  [ "monad001"
  ]

alternativeTests : TestPool
alternativeTests = MkTestPool "Free Alternative" [] Nothing
  [ "alternative001"
  ]

commitTests : TestPool
commitTests = MkTestPool "Free Alternative with Commit" [] Nothing
  [ "commit001"
  ]

main : IO ()
main = runner
  [ testPaths "monad" monadTests
  , testPaths "alternative" alternativeTests
  , testPaths "commit" commitTests
  ] where

    testPaths : String -> TestPool -> TestPool
    testPaths dir = record { testCases $= map ((dir ++ "/") ++) }
