-- | Decide what to do.
--
-- Overall design policy:
--
-- * All intermediate-languages should be interpretable in 'IO' monad with exactly same behavior.
--
--
-- [1. Interpreter]
--   interpret given code.
--
-- [2. Compiler]
--   compile given code into /brainfuck/.
--
-- In both modes, detailed error-checking using GHC are available via --with-ghc switch.
module Main where
import System.Environment

import Error
import Front


main=getArgs >>= execArgs

execArgs as
    |elem "--version" as = showVersion
    |elem "--help" as = showHelp
    |elem "--run"  as = run as
    |elem "--make" as = make as
    |otherwise = showHelp

showVersion=putStr $ unlines ["version 0.1"]

showHelp=putStr $ unlines
    ["Usage: hs2bf <command>"
    ,""
    ,"command:"
    ,"  --version: show version"
    ,"  --run <module> <common-option>*: show <module>"
    ,"  --make <module> <common-option>*: compile <module>"
    ,""
    ,"common-option:"
    ,"  -O: enable optimization"
    ,"  -Sc:  to Core code"
    ,"  -Sm:  to GMachine"
    ,"  -Sbn: to BF(n)"
    ]

run ("--run":mod:opts)=do
    putStrLn "--run is not supported yet"
run _=putStrLn "illegal options for --run"

make ("--make":mod:opts)=do
    collectModules (modToPath mod)
    
make _=putStrLn "illegal options for --make"



modToPath :: String -> IO FilePath
modToPath name=return $ "./"++name++".hs"

