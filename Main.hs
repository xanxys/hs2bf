-- | Decide what to do.
--
-- [1. Interpreter]
--   interpret given code.
--
-- [2. Compiler]
--   compile given code into /brainfuck/.
--
-- In both modes, detailed error-checking using GHC are available via --with-ghc switch.
module Main where
-- import Control.Monad
import Front


main=do
    collectModules "./test/ComplexFibonacci.hs"



