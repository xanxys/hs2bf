# hs2bf - Haskell to brainfuck compiler

## Overview
hs2bf compiles **Haskell to Brainfuck**, not the other way around.

Although it's far from Haskell98, it has lots of Haskell's distinctive features
such as ADTs and lazy evaluation.

### Language Features

* Algebraic data type
* Pattern matching
* Case expression
* Lambda expression
* Function declaration
* Infix operators
* Lazy semantics
* Numeric type `Byte` and some primitive ops
* ...

Basically, hs2bf has everything that make code look Haskell-ish.


### Runtime System Features

* Copy Garbage Collection
* 1 byte address for heap "nodes" 

Although number of heap nodes is very limited, it's not fundamental limit
and is fairly straightforward (although time-consuming) work to extend it to
any number of nodes.

The main hurdle is slow execution speed (and long turn around time when debugging).


### Missing Features

* IO monad (instead, hs2bf has a built-in type `E` to express all possible IO in CPS style)
* Type inference & polymorphism (see note below)
* class / instance definition
* Proper module system
* Most of Prelude

Lacking explicit support for polymorphism doesn't mean you can't use
polymorphic functions. For example, `map :: (a -> b) -> [a] -> [b]` works erfectly fine for any `a` or `b` in hs2bf. It merely can't **prove** the correctness of the types when compiling. (You know, a type system is a contraint on pure lambda.)

But lack of class/instance does mean you can't do things like `show :: Show a => a -> String` or `forall`.


## Compilation & Testing
Run `./conv` followed by `./auto-test` (you'll need fish shell for both).

If it's ok, the result will look like below (the runtime may differ):

```
=== test/Halt.hs ===
71330 steps
user:0.00 sys:0.00
PASSED

=== test/Const.hs ===
2422548 steps
user:0.01 sys:0.00
PASSED

=== test/ExplicitCase.hs ===
2873704 steps
user:0.02 sys:0.00
PASSED

=== test/Hello.hs ===
540952260 steps
user:2.82 sys:0.00
PASSED

=== test/LocalFun.hs ===
14103014 steps
user:0.08 sys:0.00
PASSED

=== test/Lambda.hs ===
12416333 steps
user:0.07 sys:0.00
PASSED

=== test/Arithmetic.hs ===
441625467 steps
user:2.27 sys:0.00
PASSED

=== test/ShowList.hs ===
1031462671 steps
user:5.36 sys:0.00
PASSED

=== test/QuickSort.hs ===
28503865233 steps
user:144.20 sys:0.17
PASSED
```
