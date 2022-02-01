module Free.Alternative2

import Data.List
import Data.List1
import Data.Maybe
import Data.DPair
import Data.SnocList
import Free.Common
import Free.Examples

%default total

public export
data Free : Pred Type -> Pred Type
BCont : Pred Type -> Rel Type

data Free : Pred Type -> Pred Type where
  Pure : a -> Free m a
  Lift : m a -> Free m a
  Alts : List (Free m a) -> Free m a
  Bind : Free m a -> BCont m a b -> Free m b

BCont m = Bwd (Kleisli (Free m))

export
bind : Free m a -> (a -> Free m b) -> Free m b
bind (Pure a)   f = f a
bind (Bind m k) f = Bind m (k :< f)
bind (Alts [])  f = Alts []
bind m          f = Bind m (BNil :< f)

export
Functor (Free m) where
  map f t = bind t (Pure . f)

export
Applicative (Free m) where
  pure = Pure
  fs <*> xs = bind fs $ \ f => map (f $) xs

export
Monad (Free m) where
  (>>=) = bind

export
fail : Free m a
fail = Alts []

export
union : Free m a -> Free m a -> Free m a
union m@(Pure _) n = m
union m@(Lift _) n = m
union (Alts ms) (Alts []) = Alts ms
union (Alts ms) (Alts ns) = Alts (ms ++ ns)
union (Alts ms) n         = Alts (ms ++ [n])
union m         (Alts ns) = Alts (m :: ns)
union m n = Alts [m,n]

export
Alternative (Free m) where
  empty = fail
  m <|> n = union m n

export
FCont1 : Pred Type -> Rel Type
FCont1 m = Fwd1 (Kleisli (Free m))

export
FCont : Pred Type -> Rel Type
FCont m = Fwd (Kleisli (Free m))

export
data Stack : Pred Type -> Rel Type where
  ||| Empty stack: return the result of the i-computation
  Empty : Stack m i i
  ||| Handlers in case the current i-computation fails
  Hdls  : List1 (Free m i) -> Stack m i j -> Stack m i j
  ||| Continuations turning the i-computation into a j-computation
  Cont  : FCont1 m i j -> Stack m j k -> Stack m i k

||| Push some continuations on the stack, merge with any existing Cont layer
export
push : FCont m i j -> Stack m j k -> Stack m i k
push FNil      stk            = stk
push fs        (Cont kks stk) = Cont (fs ++ kks) stk
push (f :> fs) stk            = Cont (f :> fs) stk

||| Smart constructor for Cont, checking the list is non-empty
cont : FCont m i j -> Stack m j k -> Stack m i k
cont FNil stk = stk
cont (k :> ks) stk = Cont (k :> ks) stk

||| Install handlers on the stack, merge with any existing Hdls layer
export
install : List (Free m i) -> Stack m i j -> Stack m i j
install []        stk           = stk
install ms        (Hdls ns stk) = Hdls (lappend ms ns) stk
install (m :: ms) stk           = Hdls (m ::: ms) stk

||| Smart constructor for Hdls, making sure the list is non-empty
hdls : List (Free m i) -> Stack m i j -> Stack m i j
hdls [] stk = stk
hdls (m :: ms) stk = Hdls (m ::: ms) stk

export
homo : Monad n =>
       (     m ~> n) ->
       (Free m ~> n . Maybe)
homo f t = free t Empty where

  ||| Entrypoint: evaluating an i-computation against an (i,j)-stack
  free     : Free m i -> Stack m i j -> n (Maybe j)
  ||| Continuation: confronting an i-value to an (i,j)-stack
  continue : i        -> Stack m i j -> n (Maybe j)
  ||| Handling: recovering from an i-failure in an (i,j)-stack
  handle   :             Stack m i j -> n (Maybe j)

  free (Pure a)         stk = continue a stk
  free (Lift m)         stk = f m >>= \ x => continue x stk
  free (Alts [])        stk = handle stk
  free (Alts (m :: ms)) stk = free m (install ms stk)
  free (Bind m f)       stk = free m (push (reverse f) stk)

  continue a Empty          = pure (Just a)
  continue a (Hdls _   stk) = continue a stk
  continue a (Cont (k :> ks) stk) = assert_total $ free (k a) (cont ks stk)

  handle Empty          = pure Nothing
  handle (Cont _   stk) = handle stk
  handle (Hdls (m ::: mss) stk) = assert_total $ free m (hdls mss stk)

export
run : Show a => Free Eff a -> IO ()
run prog = do
  res <- homo eff prog
  putStrLn $ "Result: \{show res}"

export
Effy (Free Eff) where lift = Lift
