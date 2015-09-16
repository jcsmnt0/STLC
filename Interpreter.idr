module Main

import Control.Catchable
import Control.Monad.State
import Data.Vect

import Parser
import ParseSyntax
import Partial
import PiVect
import Primitives
import Scopecheck
import Show
import Syntax
import Term
import Ty
import Typecheck

import Util.Either
import Util.Ex

%default partial

interpretSyn :
  (Monad m, Catchable m String, Catchable m TypeError) =>
  {as : Vect n Ty} ->
  Vect n String ->
  PiVect Val as ->
  Syn d ->
  m (Ex Val)
interpretSyn {as = as} names vals s = do
  db <- scopecheck (names ++ builtinNames) s
  E {x = a} tm <- typecheck (as ++ builtinTys) db
  return $ E $ impatience $ eval (vals ++ builtinVals) tm

Env : Type
Env = Ex $ \n => (Vect n String, (as : Vect n Ty ** PiVect Val as))

nilEnv : Env
nilEnv = E ([], ([] ** []))

-- todo: this can definitely be less redundant
interpret :
  (MonadState Env m, Catchable m String, Catchable m TypeError, Monad m) =>
  List (String, Ex Syn) ->
  m String
interpret [] = return "nothing to interpret"
interpret [(_, E s)] = do
  E (names, (as ** vals)) <- get
  E {x = a} v <- interpretSyn names vals s
  return (show v ++ " : " ++ show a)
interpret ((name, E s) :: ss) = do
  E (names, (as ** vals)) <- get
  E {x = a} v <- interpretSyn names vals s
  put (E $ (name :: names, (a :: as ** v :: vals)))
  interpret ss

instance [monadStateT] (MonadTrans t, Monad m, Monad (t m), MonadState s m) => MonadState s (t m) where
  get = lift get
  put = lift . put

Interpreter : Type -> Type
Interpreter = EitherT (Either String TypeError) $ StateT Env Identity

runInterpreter : Env -> Interpreter a -> (Either (Either String TypeError) a, Env)
runInterpreter env = runIdentity . flip runStateT env . runEitherT

execInterpreter : Env -> Interpreter a -> Either (Either String TypeError) a
execInterpreter env = fst . runInterpreter env

interpretSrc : String -> Interpreter String
-- shouldn't Idris be able to find monadStateT in instance search here?
interpretSrc src = execParser (sep1 spaces1 parseDef) src >>= interpret @{monadStateT}

execFile : String -> IO ()
-- this is not the most readable thing
execFile file = readFile file >>= putStrLn . either (either id show) id . execInterpreter nilEnv . interpretSrc
