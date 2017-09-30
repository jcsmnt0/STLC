module Main

import Control.Catchable
import Control.Monad.State
import Data.Vect
import Data.Vect.Quantifiers

import Term.Typecheck
import Term.Parse
import Term.Raw
import Ty.Raw
import Ty.Scoped
import Ty.Val

import BuiltIns
import Interpreter
import Show

import Parser
import Util.Catcher
import Util.Ex
import Util.Monad

covering handle' : Catcher Errors a -> IO (Maybe a)
handle' x = handle [\x => putStrLn x >> pure Nothing, \x => printLn x >> pure Nothing] (pure . Just <$> x)

covering builtinEnv' : IO (Maybe Env)
builtinEnv' = handle' $ execInterpreter nilEnv (builtinEnv @{monadStateT})

-- the Show instance for FileError isn't covering, apparently
execFile : String -> IO ()
execFile file = do
  Right src <- readFile file | Left err => putStrLn ("IO error: " ++ show err)
  Just env <- builtinEnv' | _ => putStrLn ("stdlib error")
  putStrLn $ handle [id, show] $ execInterpreter env $ interpretSrc src

covering rep : IO Bool
rep = do
  src <- getLine
  if src == "exit"
    then pure True
    else do
      Just (E t) <- handle' $ execParser parseTerm src | _ => pure False
      Just env <- builtinEnv' | _ => pure False
      Just t' <- handle' $ interpretSyn env t | _ => pure False
      putStrLn $ showExVal t'
      pure False

covering repl : IO ()
repl = putStrLn "hello\n" *> until id (rep <* putStrLn "") *> pure ()

main : IO ()
main = do
  case !getArgs of
    [_] => repl
    [_, file] => execFile file
    _ => putStrLn "unsupported argument list"
