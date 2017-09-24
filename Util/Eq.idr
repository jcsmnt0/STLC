module Util.Eq

%default total

%access export

cong2 : {a, b, c : Type} -> {f : a -> b -> c} -> {x, y : a} -> {z, w : b} -> x = y -> z = w -> f x z = f y w
cong2 Refl Refl = Refl

replacePreservesEquality : {P : a -> Type} -> (x : P u) -> (p : u = v) -> x = replace {P = P} p x
replacePreservesEquality x Refl = Refl

replace' : a = b -> a -> b
replace' = replace {P = id}

-- this is a hack to get around what seems to be an Idris runtime bug:
-- if a module imports Util.LTE, which also exports a function called trans, Idris won't confuse it with the built-in
-- trans function at compile time, but will throw a "Multiple definitions found for trans" error at runtime.
-- there doesn't seem to be a way to explicitly qualify the built-in trans function, since it's not defined in a named
-- module, so this is just redefining it so it can be referred to as Eq.trans to disambiguate.
trans : a = b -> b = c -> a = c
trans Refl Refl = Refl
