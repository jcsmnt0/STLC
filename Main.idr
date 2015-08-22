module Main

import Data.Vect

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

%default partial

eval : String -> Either String (d ** (ty ** Term d builtinTys ty))
eval src =  do
  MkResult (E s) rest <- runParser parseSyn src
  db <- scopecheck builtinNames s
  E tm <- mapLeft show (typecheck builtinTys db)
  return (_ ** (_ ** tm))

rep : IO Bool
rep = do
  src <- getLine
  if src == "exit"
     then return True
     else
       case eval src of
         Left err => putStrLn err *> return False
         Right (_ ** (ty ** tm)) => do
           putStrLn ("\n" ++ show tm ++ " : " ++ show ty)
           putStrLn "=>"
           putStrLn (show (impatience (eval builtinVals tm)))
           return False

main : IO ()
main = putStrLn "hello\n" *> until id (rep <* putStrLn "") *> return ()
