import Free.Common
import Free.Examples

import Free.Commit

test : IO ()
test = do
  run cat3
  run cat3
  run countdown
