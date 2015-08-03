module Main

import Data.Vect

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

import Util.Monad

%default partial

readBox : String -> JS_IO String
readBox s = foreign FFI_JS "document.getElementById(%0).value" (String -> JS_IO String) s

putBox : String -> String -> JS_IO ()
putBox id str = foreign FFI_JS "document.getElementById(%0).innerHTML += %1 + '<br>'" (String -> String -> JS_IO ()) id str

rep : JS_IO ()
rep = do
  src <- getLine
  if src == ""
     then return ()
     else
       -- every step should return an Either, this is ugly
       case runParser parseSyn (unpack src) of
         Nothing => putBox "out" ("bad syntax: " ++ show src)
         Just (s, rest) =>
           let (_ ** sc) = tagDepth s in
             case scopecheck builtinNames sc of
               Left err => putBox "out" ("bad scope: " ++ show err)
               Right db =>
                 case typecheck builtinTys db of
                   Nothing => putBox "out" ("bad types: " ++ show db)
                   Just (ty ** tm) => do
                     putBox "out" ("\n" ++ show tm ++ " : " ++ show ty)
                     putBox "out" "=>"
                     putBox "out" (show (impatience (eval builtinVals tm)))

main : JS_IO ()
main = putBox "out" "hello\n" *> forever (rep *> putStrLn "")
