import Free.Common
import Free.Examples

import Free.Alternative2

test : IO ()
test = do
  run getNonEmpty
  run getNonEmpty
  run getNonEmpty
  run noBacktracking
