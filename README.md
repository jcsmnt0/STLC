# Overview
This repository contains a parser, scope checker, type checker, and big-step evaluator for simply typed lambda calculus with a few extensions. (The core term language and evaluator actually support universally quantified variables and substitution at the type level, but there's no syntax or typechecking for that feature yet.) The evaluator is correct by construction with respect to type preservation, which means evaluating a term is guaranteed to produce a value of the same type or diverge.

I'm developing this mostly as a learning exercise, so it's extremely bare at the moment. That said, the few features it does have are fully usable and run reasonably quickly.

# Language Features
- Built-in types: Num (natural numbers), Bool
- Tuple types
- Sum types
- General recursion
- Idris values/functions can be imported as primitives

# Syntax
All subject to change on a whim, or even possibly for good reasons.

- Identifiers are made up of letters or any of ``+=<>_!@#$%^&*-|'"?/`~``
- Bool literals
  - `true`, `false`
- Num literals
  - `1000`
- `if`/`then`/`else`
  - `if true then 1 else 0`
  - Branches are lazily evaluated
- `let` bindings
  - `let x = + 1 3 in x`
- Type annotation
  - `+ (1 : Num) 3`
- Function application
  - `f x`
- Lambdas
  - `\x: Num. + 1 x`
  - Argument type is required
- Recursive functions
  - `fn factorial(x: Num): Num. if (|| (== x 0) (== x 1)) then 1 else (* x (factorial (pred x)))`
  - Function name, argument type, and return type are required
- Tuples
  - Type
    - `(Num, Bool)`
  - Construction
    - `(3, true)`
  - Unpacking
    - `let (x, y) = z in + x y`
- Sums
  - Type
    - `(Num | Bool)`
  - Construction
    - `variant 0 3 : (Num | Bool)`, `variant 1 true : (Num | Bool)`
    - `variant` always requires an explicit type annotation
    - The first argument to `variant` indicates which variant of the sum type is being constructed - i.e. a sum type is a list of types, and the first argument is an index into that list. This is to allow sum types with multiple variants of the same type: `variant 0 true : (Bool | Bool)` is distinct from `variant 1 true : (Bool | Bool)`.
  - Casing
    - Assuming `x : (Num | Bool)`, `case x of { \a: Num. iszero a; \b: Bool => b } : Bool`
    - Curly braces contain a a list of functions whose argument types correspond to the components of the sum type in order
    - Semicolon after the last branch is optional

# How to build
Just run `idris --build stlc.ipkg` and wait for the `stlc` executable to come into being. This code is tested against Idris 0.10.

# REPL
A REPL launches when you run `stlc` with no arguments. Type in an expression and hit Enter to receive the evaluated result. Once you're bored of that, enter `exit` to exit.

# Running programs
Run `stlc <file>` to run the interpreter over a program. Programs are made up of whitespace-separated definitions, which look like `def <name> = <expr>`. The output of the interpreter is the result of evaluating the last definition in the file, so e.g. the program

    def x = 3
    def y = 4
    def z = + x y
prints out "7" when interpreted.
