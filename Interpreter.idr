module Interpreter

import Control.Catchable
import Control.Monad.State
import Data.Vect

import Parser
import ParseSyntax
import Partial
import PVect
import Primitives
import Scopecheck
import Show
import Syntax
import Term
import Ty
import Typecheck

import Util.Catcher
import Util.Either
import Util.Elem
import Util.Ex

%default partial

interpretSyn :
  (Monad m, Catchable m String, Catchable m TypeError) =>
  {as : Vect n Ty} ->
  Vect n String ->
  PVect Val as ->
  Syn d ->
  m (Ex Val)
interpretSyn {as = as} names vals s = do
  sc <- scopecheck (names ++ builtinNames) s
  E {x = a} tm <- typecheck (as ++ builtinTys) sc
  return $ E $ impatience $ eval (vals ++ builtinVals) tm

Env : Type
Env = Ex $ \n => (Vect n String, (as : Vect n Ty ** PVect Val as))

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
  return (showVal v ++ " : " ++ show a)
interpret ((name, E s) :: ss) = do
  E (names, (as ** vals)) <- get
  E {x = a} v <- interpretSyn names vals s
  put (E $ (name :: names, (a :: as ** v :: vals)))
  interpret ss

[monadStateT] (MonadTrans t, Monad m, Monad (t m), MonadState s m) => MonadState s (t m) where
  get = lift get
  put = lift . put

Errors : Vect 2 Type
Errors = [String, TypeError]

Interpreter : Type -> Type
Interpreter = CatcherT Errors $ StateT Env Identity

runInterpreter : Env -> Interpreter a -> (Catcher Errors a, Env)
runInterpreter env = runIdentity . flip runStateT env . runCatcherT

execInterpreter : Env -> Interpreter a -> Catcher Errors a
execInterpreter env = fst . runInterpreter env

interpretSrc : String -> Interpreter String
-- shouldn't Idris be able to find monadStateT in instance search here?
interpretSrc src = execParser (sep1 spaces1 parseDef) src >>= interpret @{monadStateT}

execFile : String -> IO ()
execFile file = do
  Right src <- readFile file | Left err => putStrLn ("IO error: " ++ show err)
  putStrLn $ handle [id, show] $ execInterpreter nilEnv $ interpretSrc src
