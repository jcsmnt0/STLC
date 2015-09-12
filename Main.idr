module Main

import Control.Catchable
import Data.Vect

import Interpreter
import ParseSyntax
import Parser
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
import Util.Monad

covering re : String -> Either String (Ex Val)
re src = do
  E s <- execParser parseSyn src
  interpretSyn [] [] s

covering rep : IO Bool
rep = do
  src <- getLine
  if src == "exit"
    then return True
    else
      case re src of
        Left err => putStrLn err *> return False
        Right (E {x = a} t) => putStrLn (show t ++ " : " ++ show a) *> return False

covering repl : IO ()
repl = putStrLn "hello\n" *> until id (rep <* putStrLn "") *> return ()

partial main : IO ()
main = do
  args <- getArgs
  case args of
    [_] => repl
    [_, file] => execFile file
