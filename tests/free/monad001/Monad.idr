import Free.Common
import Free.Examples

import Free.Monad

test : IO ()
test = do
  -- the other tests are returning a `Maybe`-value
  -- so for uniformity we adjust the output here
  run $ Just <$> cat3
  run $ Just <$> cat3
  run $ Just <$> countdown
