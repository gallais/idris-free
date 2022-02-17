module Free.Mixed

import Data.Bool
import Data.List
import Data.List1
import Data.Maybe
import Data.DPair
import Free.Common
import Free.Examples

%default total

||| This type of generalised relations has two inputs & two outputs:
||| * A boolean that will be used to track whether corecursive calls are allowed
||| * A value of type `a`, just like any other relation (it will be Type in our development)
GRel : Type -> Type
GRel a = Bool -> a ->
         Bool -> a ->
         Type

namespace Bwd

  ||| Left-nested type-aligned sequences
  public export
  data Bwd : GRel a -> GRel a where
    BNil : Bwd r g a g a
    (:<) : Bwd r g a h b -> r h b i c -> Bwd r g a i c

namespace Bwd1

  ||| Non-empty left-nested type-aligned sequences
  public export
  data Bwd1 : GRel a -> GRel a where
    (:<) : Bwd r g a h b -> r h b i c -> Bwd1 r g a i c

  export
  forget : Bwd1 r g a h b -> Bwd r g a h b
  forget (p :< ps) = p :< ps

namespace Fwd

  ||| Right-nested type-aligned sequences
  public export
  data Fwd : GRel a -> GRel a where
    FNil : Fwd r g a g a
    (:>) : {0 r : GRel _} -> r g a h b -> Fwd r h b i c -> Fwd r g a i c

namespace Fwd1

  ||| Non-empty right-nested type-aligned sequences
  public export
  data Fwd1 : GRel a -> GRel a where
    (:>) : {0 r : GRel _} -> r g a h b -> Fwd r h b i c -> Fwd1 r g a i c

  export
  forget : Fwd1 r g a h b -> Fwd r g a h b
  forget (ps :> p) = ps :> p

  ||| chips: unloading a left-nested type-aligned sequence onto a right-nested one
  export
  (<>>) : Bwd r g a h b -> Fwd1 r h b i c -> Fwd1 r g a i c
  BNil      <>> fs = fs
  (bs :< b) <>> fs = bs <>> (b :> forget fs)

  ||| Reassociate a left-nested type-aligned sequence to get a right-nested one
  export
  reassociate : Bwd1 r g a h b -> Fwd1 r g a h b
  reassociate (bs :< b) = bs <>> (b :> FNil)

||| Non-empty list of value. Used for disjunctions: it is productive if
||| all the alternatives are productive
data And1 : Pred Bool -> Pred Bool where
  Last1 : p g -> And1 p g
  (::)  : p g -> And1 p h -> And1 p (g && h)

||| Generalisation of the classic notion of a Kleisli function space to accomodate
||| the tracking of productivity
data Kleisli : (Bool -> Pred Type) -> GRel Type where
  Seq   :     (a -> r h b) -> Kleisli r g    a  (g || h) b
  Then  :           r h b  -> Kleisli r g    () (g || h) b
  ISeq  : Inf (a -> r h b) -> Kleisli r True a  True     b
  IThen : Inf (     r h b) -> Kleisli r True () True     b

infixr 0 $$
||| Applying a Kleisli function to its argument.
($$) : Kleisli m f a g b -> a -> Exists $ \ h => m h b
Seq   k $$ x = Evidence _ (k x)
Then  k $$ x = Evidence _ k
ISeq  k $$ x = Evidence _ (k x)
IThen k $$ x = Evidence _ k


||| The big mixed inductive-coinductive type
data Free : (Bool -> Pred Type) -> Bool -> Pred Type
BCont : (Bool -> Pred Type) -> GRel Type

public export
data Free : (Bool -> Pred Type) -> Bool -> Pred Type where
  ||| Pure values do not consume anything
  Pure   : a -> Free m False a
  ||| Bind is the workhorse: if the first computation consumes then the
  ||| Kleislis in the BCont will be allowed to perform corecursive calls
  Bind   : Free m g a -> BCont m g a h b -> Free m h b
  ||| Lift only consumes if the lifted computation does
  Lift   : m b a -> Free m b a
  ||| Fail can get any type and lie as much as it wants about consuming:
  ||| we won't run the continuations anyway!
  Fail   : Free m g a
  ||| Alternatives use `And1` so that they are only declared consuming if
  ||| all the alternatives are
  Alts   : And1 (\ b => Free m b a) g -> Free m g a
  ||| Committing does not consume anything
  Commit : Free m False ()
  ||| Insisting that something must succeed does not change its consumption pattern
  Must   : Free m g a -> Free m g a

BCont m = Bwd1 (Kleisli (Free m))

||| Type-level function for a conditionally infinite type.
public export
inf : Bool -> Type -> Type
inf False t = t
inf True t = Inf t

export
thunk : {g : _} -> (a -> Free m h b) -> inf g (a -> Free m h b)
thunk {g = False} f = f
thunk {g = True}  f = f

export
mkSeq : {g : _} -> inf g (a -> Free m h b) -> Kleisli (Free m) g a (g || h) b
mkSeq {g = True}  = ISeq
mkSeq {g = False} = Seq

export
bind : {g : _} -> Free m g a -> inf g (a -> Free m h b) -> Free m (g || h) b
bind (Pure a)   f = f a
bind (Bind m k) f = Bind m (forget k :< mkSeq f)
bind Fail       f = Fail
bind m          f = Bind m (BNil :< mkSeq f)

export
{g : _} -> Functor (Free m g) where
  map f t = rewrite sym $ orFalseNeutral g in
            bind t (thunk (Pure . f))

export %inline
(<*>) : {g, h : _} ->
        Free m g (a -> b) ->
        Free m h a ->
        Free m (g || h) b
(<*>) x y = bind x (thunk (\ f => map f y))

export
fail : Free m g a
fail = Fail

export
-- We can't do the same fusion anymore as that would change the
-- meaning of `commit`. (<|>) associates to the right only.
union : Free m g a -> Free m h a -> Free m (g && h) a
-- left wins
union m@(Pure _) n    = m
union m@Commit   n    = m
-- the two following cases do not typecheck: we would need to be able to weaken
--      m : Free m g        a
-- to   m : Free m (g && h) a
-- union m@(Lift _) n    = m
-- union m          Fail = m
-- proper sum
union m (Alts ns) = Alts (m :: ns)
union m n = Alts (m :: Last1 n)

export
record EKleisli (m : Bool -> Pred Type) (a, b : Type) where
  constructor MkEKleisli
  {0 leftEat : Bool}
  {0 rightEat : Bool}
  eKleisli : Kleisli m leftEat a rightEat b

export
record FCont (m : Bool -> Pred Type) (a, b : Type) where
  constructor MkFCont
  {0 leftEat : Bool}
  {0 rightEat : Bool}
  fCont : Fwd1 (Kleisli (Free m)) leftEat a rightEat b

export
record FAlts (m : Bool -> Pred Type) (a : Type) where
  constructor MkFAlts
  {0 bound : Bool}
  fAlts : And1 (\ g => Free m g a) bound

-- Note that in Stack we don't care about maintaining the consumption
-- invariant. `doParse` doesn't care about it either so that's not a
-- feature loss.
-- Enforcing the invariant would be annoying for the same reason we
-- could not get `union m Fail = m` to hold: we would need to be able to
-- weaken bounds when starting to go through the alternatives in a Hdls
||| A Stack is indexed by an input and an output type.
||| The idea is that putting an (i,o)-stack against an i-computation will
||| produce an o-computation.
public export
data Stack : (Bool -> Pred Type) -> Rel Type where
  ||| Empty stack: input & output types are equal
  Empty : Stack m i i
  ||| Handlers are ways to recover is the i-computation in focus fails
  Hdls  : List (FAlts m i)   -> Stack m i j -> Stack m i j
  ||| Continuations are computations to perform after the i-computation in focus
  ||| has succeeded
  Cont  : Fwd1 (FCont m) i j -> Stack m j k -> Stack m i k

||| Insisting that a computation *must* succeed means that any error will be
||| fatal. In other words we need to uninstall all of the handlers that may
||| have been accumulated so far.
export
filterHdls : Stack m i j -> Bwd (Fwd1 (FCont m)) i j
filterHdls = go BNil where

  go : Bwd (Fwd1 (FCont m)) x y -> Stack m y z -> Bwd (Fwd1 (FCont m)) x z
  go acc Empty = acc
  go acc (Hdls _ stk) = go acc stk
  go acc (Cont fs stk) = go (acc :< fs) stk

||| Flatten starts by filtering all the handlers and then flattens the remaining
||| continuations to obtain a stack that's at most one layer deep. This means that
||| iterated `Must` commitment become extremely cheap.
export
flatten : Stack m i j -> Stack m i j
flatten stk = case filterHdls stk of
  BNil => Empty
  fss :< fs => Cont (concat (fss :< fs)) Empty

||| Push a continuation on the stack.
||| If there are local continuations already, we enqueue it.
||| Otherwise we start a new Cont layer.
export
push : FCont m i j -> Stack m j k -> Stack m i k
push fs (Cont ks stk) = Cont (fs :> forget ks) stk
push fs stk           = Cont (fs :> FNil) stk

||| Push a (potentially empty) list of continuations on the stack
export
cont : Fwd (FCont m) i j -> Stack m j k -> Stack m i k
cont FNil stk = stk
cont (fs :> fss) stk = Cont (fs :> fss) stk

||| Push a handler on the stack. We can't do any merging here because committing
||| only commits for the most local disjunction.
export
-- can't do any optimisation here because of commit
install : List (FAlts m i) -> Stack m i j -> Stack m i j
install ms = Hdls ms

||| Committing will purge the most local stash of handlers
export
uninstall : Stack m i j -> Stack m i j
uninstall (Hdls ns stk) = Hdls [] stk
uninstall (Cont fs (Hdls ns stk)) = Cont fs (Hdls [] stk)
  -- not pushing so that multiple commits do not start cancelling surrounding actions!
uninstall stk = stk

namespace List1

  export
  first : List (FAlts m i) -> Maybe ( Exists (\ g => Free m g i)
                                    , List (FAlts m i))
  first [] = Nothing
  first (MkFAlts (Last1 m) :: mss) = pure (Evidence _ m, mss)
  first (MkFAlts (m :: ms) :: mss) = pure (Evidence _ m, MkFAlts ms :: mss)

namespace Fwd1

  export
  first : Fwd1 (FCont m) i k -> Exists $ \ j =>
          (EKleisli (Free m) i j, Fwd (FCont m) j k)
  first ((MkFCont (k :> FNil)) :> kss) = Evidence _ (MkEKleisli k, kss)
  first ((MkFCont (k :> (l :> ls))) :> kss)
    = Evidence _ (MkEKleisli k, MkFCont (l :> ls) :> kss)

||| Given an interpretation of the lifted actions into a monad,
||| we can give an interpretation of a Free computation as a
||| potentially failing computation in that monad.
export
homo : Monad n =>
       (forall g, a.      m g a -> n        a) ->
       (forall g, a. Free m g a -> n (Maybe a))
homo f t = free t Empty where

  ||| Put a free i-computation against an (i, j)-stack to produce a j-computation
  free     : Free m _ i -> Stack m i j -> n (Maybe j)
  ||| Continue with an i-value against an (i, j)-stack to produce a j-computation
  continue : i          -> Stack m i j -> n (Maybe j)
  ||| Handle an error in a (i, j)-stack to produce a j-computation
  handle   :               Stack m i j -> n (Maybe j)

  free (Pure a)         stk = continue a stk
  free (Lift m)         stk = f m >>= \ x => continue x stk
  free Commit           stk = continue () (uninstall stk)
  free (Must m)         stk = free m (flatten stk)
  free Fail             stk = handle stk
  free (Alts (Last1 m)) stk = free m (install [] stk)
  free (Alts (m :: ms)) stk = free m (install [MkFAlts ms] stk)
  free (Bind m f)       stk = free m (push (MkFCont (reassociate f)) stk)

  continue a Empty          = pure (Just a)
  continue a (Hdls _   stk) = continue a stk
  continue a (Cont kss stk) = case first kss of
    (Evidence _ (MkEKleisli k, kss)) =>
      assert_total $ free (snd (k $$ a)) (cont kss stk)

  handle Empty          = pure Nothing
  handle (Cont _   stk) = handle stk
  handle (Hdls mss stk) = case first mss of
    Just (Evidence _ m, mss) => assert_total $ free m (Hdls mss stk)
    Nothing => handle stk

export
run : Show a => Free (const Eff) g a -> IO ()
run prog = do
  res <- homo eff prog
  putStrLn $ "Result: \{show res}"

export
Effy (Free (const Eff) False) where lift = Lift

------------------------------------------------------------------------------
-- Declaring these purely for testing purposes

export
Applicative (Free m False) where
  pure = Pure
  fs <*> xs = bind fs $ \ f => map (f $) xs

export
Monad (Free m False) where
  (>>=) = bind

export
Alternative (Free m False) where
  empty = fail
  m <|> n = union m n
