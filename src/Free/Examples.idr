module Free.Examples

import Data.List

--------------------------------------------------------------
-- Some effects for examples

public export
data Eff : Type -> Type where
  Get      : Eff String
  PutStrLn : String -> Eff ()

export
eff : Eff a -> IO a
eff = \case
  Get          => getLine
  PutStrLn str => putStrLn str

public export
interface Effy m where
  lift : Eff a -> m a

export
get : Effy m => m String
get = lift Get

export
putStrLn : Effy m => String -> m ()
putStrLn = lift . PutStrLn

--------------------------------------------------------------
-- With monad constraint

export
cat3 : (Monad m, Effy m) => m ()
cat3 = sequence_ (replicate 3 $ putStrLn =<< get)

export
echo : (Monad m, Effy m) => Nat -> m Nat
echo n = do
  putStrLn ("Passing " ++ show n)
  pure n

--------------------------------------------------------------
-- With monad & alternative constraints

export
error : (Monad m, Alternative m, Effy m) => String -> m a
error err = do
  putStrLn err
  empty

export
nonEmpty : (Monad m, Alternative m, Effy m) => m ()
nonEmpty = do
  putStrLn "Input"
  n <- get
  guard (n /= "")
  putStrLn n
