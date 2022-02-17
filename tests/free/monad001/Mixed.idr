import Free.Common
import Free.Examples

import Free.Mixed

test : IO ()
test = do
  run {g = False} cat3
  run {g = False} cat3
  run {g = False} countdown
