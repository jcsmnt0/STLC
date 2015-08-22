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

import Util.Ex
import Util.Monad

%default partial

eval : String -> Either String (d ** (ty ** Term d builtinTys ty))
eval src = 
 case runParser parseSyn src of
   Left err => Left ("bad syntax: " ++ err)
   Right (MkResult (E s) rest) =>
       case scopecheck builtinNames s of
         Left err => Left ("bad scope: " ++ err)
         Right db =>
           case typecheck builtinTys db of
             Nothing => Left ("bad types: " ++ show db)
             Just (E tm) => Right (_ ** (_ ** tm))

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
