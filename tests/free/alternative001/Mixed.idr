import Free.Common
import Free.Examples

import Free.Mixed

test : IO ()
test = do
  run getNonEmpty
  run getNonEmpty
  run getNonEmpty
  run noBacktracking
