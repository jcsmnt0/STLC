module Main

import Control.Catchable
import Control.Monad.Identity
import Data.Vect
import Data.Vect.Quantifiers

import Interpreter
import ParseSyntax
import Parser
import Partial
import Primitives
import Scopecheck
import Show
import Syntax
import Term
import Ty
import Typecheck

import Util.Catcher
import Util.Either
import Util.Ex
import Util.Monad

covering re : String -> Catcher [String, TypeError] (Ex Val)
re src = do
  E s <- execParser parseSyn src
  interpretSyn [] [] s

covering rep : IO Bool
rep = do
  src <- getLine
  if src == "exit"
    then return True
    else (putStrLn $ handle [id, show] $ map showExVal (re src)) *> return False

covering repl : IO ()
repl = putStrLn "hello\n" *> until id (rep <* putStrLn "") *> return ()

partial main : IO ()
main = do
  case !getArgs of
    [_] => repl
    [_, file] => execFile file
