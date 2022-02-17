import Free.Common
import Free.Examples

import Free.Mixed

test : IO ()
test = do
  run getNonEmptyCommit
  run getNonEmptyCommit
  run getNonEmptyCommit
  run doubleCommit
  run mustFail
