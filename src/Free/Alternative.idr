module Free.Alternative

import Data.List
import Data.List1
import Data.Maybe
import Data.DPair
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

BCont m = Bwd (\a, b => a -> Free m b)

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
FCont : Pred Type -> Rel Type
FCont m = Fwd1 (Kleisli (Free m))

export
data Stack : Pred Type -> Rel Type where
  Empty : Stack m i i
  Hdls  : List1 (List1 (Free m i)) -> Stack m i j -> Stack m i j
  Cont  : Fwd1 (FCont m) i j -> Stack m j k -> Stack m i k

export
push : Fwd (Kleisli (Free m)) i j -> Stack m j k -> Stack m i k
push FNil      stk                  = stk
push (f :> fs) (Cont (k :> ks) stk) = Cont ((f :> fs) :> (k :> ks)) stk
push (f :> fs) stk                  = Cont ((f :> fs) :> FNil) stk

export
cont : Fwd (FCont m) i j -> Stack m j k -> Stack m i k
cont FNil stk = stk
cont (fs :> fss) stk = Cont (fs :> fss) stk

export
install : List (Free m i) -> Stack m i j -> Stack m i j
install []        stk           = stk
install (m :: ms) (Hdls ns stk) = Hdls ((m ::: ms) ::: forget ns) stk
install (m :: ms) stk           = Hdls ((m ::: ms) ::: []) stk

export
hdls : List (List1 (Free m i)) -> Stack m i j -> Stack m i j
hdls [] stk = stk
hdls (ms :: mss) stk = Hdls (ms ::: mss) stk

namespace List1

  export
  first : List1 (List1 a) -> (a, List (List1 a))
  first ((m ::: []) ::: mss) = (m, mss)
  first ((m ::: (n :: ns)) ::: mss) = (m, (n ::: ns) :: mss)

namespace Fwd1

  export
  first : Fwd1 (Fwd1 r) i k -> Exists $ \ j =>
          (r i j, Fwd (Fwd1 r) j k)
  first ((k :> FNil) :> kss) = Evidence _ (k, kss)
  first ((k :> (l :> ls)) :> kss) = Evidence _ (k, (l :> ls) :> kss)

export
homo : Monad n =>
       ({0 a : Type} ->      m a -> n        a) ->
       ({0 a : Type} -> Free m a -> n (Maybe a))
homo f t = free t Empty where

  free     : Free m i -> Stack m i j -> n (Maybe j)
  continue : i        -> Stack m i j -> n (Maybe j)
  handle   :             Stack m i j -> n (Maybe j)

  free (Pure a)         stk = continue a stk
  free (Lift m)         stk = f m >>= \ x => continue x stk
  free (Alts [])        stk = handle stk
  free (Alts (m :: ms)) stk = free m (install ms stk)
  free (Bind m f)       stk = free m (push (reverse f) stk)

  continue a Empty          = pure (Just a)
  continue a (Hdls _   stk) = continue a stk
  continue a (Cont kss stk) = case first kss of
    (Evidence _ (k, kss)) => assert_total $ free (k a) (cont kss stk)

  handle Empty          = pure Nothing
  handle (Cont _   stk) = handle stk
  handle (Hdls mss stk) = case first mss of
    (m, mss) => assert_total $ free m (hdls mss stk)

export
run : Free Eff () -> IO ()
run prog = ignore $ homo eff prog

export
Effy (Free Eff) where lift = Lift
