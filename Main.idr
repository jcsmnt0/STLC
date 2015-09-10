module Main

import Data.Vect
import Debug.Trace

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

eval : String -> Either String String
eval src =  do
  MkResult (E s) rest <- runParser parseSyn src
  db <- scopecheck builtinNames s
  E {x = ty} tm <- mapLeft show (typecheck builtinTys db)
  trace (show tm) $ return ()
  trace (show ty) $ return ()
  return $ "\n" ++ show tm ++ " : " ++ show ty ++ "\n=>\n" ++ show (impatience (eval builtinVals tm))

rep : IO Bool
rep = do
  src <- getLine
  if src == "exit"
     then return True
     else putStrLn (collapse (eval src)) *> return False

main : IO ()
main = putStrLn "hello\n" *> until id (rep <* putStrLn "") *> return ()
