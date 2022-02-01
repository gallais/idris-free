module Free.Examples

import Data.List

--------------------------------------------------------------
-- Some effects for examples

public export
data Eff : Type -> Type where
  Get      : Eff String
  PutStr   : String -> Eff ()
  PutStrLn : String -> Eff ()

export
eff : Eff a -> IO a
eff = \case
  Get          => getLine
  PutStr str   => putStr str
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

export
putStr : Effy m => String -> m ()
putStr = lift . PutStr

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

export
countdown : (Monad m, Effy m) => m ()
countdown = do
  ignore $ echo 3
  ignore $ echo 2
  ignore $ echo 1
  putStrLn "boom"

--------------------------------------------------------------
-- With monad & alternative constraints

export
error : (Monad m, Alternative m, Effy m) => String -> m a
error err = do
  putStrLn err
  empty

export
nonEmpty : (Monad m, Alternative m, Effy m) => m ()
nonEmpty = (<|> (putStrLn "" *> empty)) $ do
  putStr "Input: "
  n <- get
  guard (n /= "")
  putStrLn n

export
getNonEmpty : (Monad m, Alternative m, Effy m) => m ()
getNonEmpty = sequence_ (replicate 3 nonEmpty)
   <|> error "Failed!"
   <|> putStrLn "Ouch: error in the error handler!"
   <|> putStrLn "This better not show up!"

export
noBacktracking : (Monad m, Alternative m, Effy m) => m ()
noBacktracking =
  do n <- (error "Not here" <|> echo Z <|> echo (S Z))
     if n /= Z
       then putStrLn "Ouch: backtracked and got: \{show n}"
       else error "No backtracking in the bind"
