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

rep : IO ()
rep = do
  src <- getLine
  if src == ""
     then return ()
     else
       case runParser parseSyn (unpack src) of
         Left err => putStrLn ("bad syntax: " ++ show err)
         Right (MkResult (E s) rest _) =>
             case scopecheck builtinNames s of
               Left err => putStrLn ("bad scope: " ++ show err)
               Right db =>
                 case typecheck builtinTys db of
                   Nothing => putStrLn ("bad types: " ++ show db)
                   Just (ty ** tm) => do
                     putStrLn ("\n" ++ show tm ++ " : " ++ show ty)
                     putStrLn "=>"
                     putStrLn (show (impatience (eval builtinVals tm)))

main : IO ()
main = putStrLn "hello\n" *> forever (rep *> putStrLn "")
