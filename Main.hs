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
import Language.Haskell.Pretty
import System.Environment
import System.FilePath.Posix

import Error
import Front
import Core
import GMachine
import Brainfuck


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
    let lang=analyzeOpt opts
    let (modname,env)=analyzeName mod
    
    x<-collectModules env modname
    case x of
        Left es -> putStr $ unlines $ map show es
        Right [m] ->
            putStrLn (prettyPrint (mds $ wds m)) >> putStrLn "\n==========\n" >>
            putStrLn (pprintCoreP (sds $ mds $ wds m)) >> putStrLn "\n==========\n"
make _=putStrLn "illegal options for --make"


analyzeName :: String -> (String,ModuleEnv)
analyzeName n=(takeBaseName n,ModuleEnv [dirPrefix++takeDirectory n])
    where dirPrefix=if isAbsolute n then "" else "./"


analyzeOpt :: [String] -> Language
analyzeOpt []=LangBF0
analyzeOpt ("-Sc":xs)=LangCore
analyzeOpt ("-Sm":xs)=LangGMachine
analyzeOpt ("-Sb0":xs)=LangBF0
analyzeOpt (x:xs)=analyzeOpt xs





data Language
    =LangCore
    |LangGMachine
    |LangBF0
    deriving(Show,Eq,Ord)


