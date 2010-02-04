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
import Control.Monad
import Language.Haskell.Pretty
import System.Environment
import System.FilePath.Posix

import Util
import qualified Front
import qualified Core
import qualified GMachine
import qualified Brainfuck


main=execCommand =<< liftM parseArgs getArgs

-- | Complete description of /hs2bf/ behavior
data Command
    =ShowMessage String
    |Interpret Option String
    |Compile Option String

data Language
    =LangCore
    |LangGMachine
    |LangBF0
    deriving(Show,Eq,Ord)

-- | All /global options/
data Option=Option
    {optimize :: Bool
    ,bfAddrSpace :: Int
    ,verbose :: Bool
    ,debug :: Bool
    ,tolang :: Language
    }

-- | Parse arguments to 'Command'. Note this is a total function.
parseArgs :: [String] -> Command
parseArgs []=ShowMessage version
parseArgs ("-v":_)=ShowMessage version
parseArgs ("--version":_)=ShowMessage version
parseArgs ("-h":_)=ShowMessage $ version++"\n"++help
parseArgs ("--help":_)=ShowMessage $ version++"\n"++help
parseArgs ("--run":n:as)=Interpret (parseOption as) n
parseArgs ("--make":n:as)=Compile (parseOption as) n
parseArgs _=ShowMessage "Invalid command. See 'hs2bf --help' for usage."



parseOption :: [String] -> Option
parseOption []=Option{optimize=False,bfAddrSpace=2,verbose=True,debug=False,tolang=LangBF0}
parseOption (term:xs)=case term of
    "-O" -> o{optimize=True}
    "-Sc" -> o{tolang=LangCore}
    "-Sg" -> o{tolang=LangGMachine}
    "-Sb0" -> o{tolang=LangBF0}
    _ -> error $ "unknown option:"++term
    where o=parseOption xs





execCommand :: Command -> IO ()
execCommand (ShowMessage x)=putStr x
execCommand (Interpret opt from)=undefined
execCommand (Compile opt from)=do
    let (mod,env)=analyzeName from
    xs<-Front.collectModules env mod
    case tolang opt of
        LangCore -> outputWith Core.pprintCoreP $ runProcess $ xs >>= Front.compile
        LangGMachine -> outputWith GMachine.pprintGM $ runProcess $ xs >>= Front.compile >>= Core.compile
        LangBF0 ->  outputWith show $ runProcess $ xs >>= Front.compile >>= Core.compile >>= GMachine.compile
    where
        outputWith :: (a->String) -> Either [CompileError] a -> IO ()
        outputWith f=putStr . either (unlines . map show) f


version :: String
version="version 0.1\n"

help :: String
help=unlines $
    ["Usage: hs2bf <command>"
    ,""
    ,"command:"
    ,"  --version: show version"
    ,"  --run <module> <option>*: show <module>"
    ,"  --make <module> <option>*: compile <module>"
    ,""
    ,"option:"
   -- ,"  --verbose: show internal data (for hs2bf devloppers)"
    ,"  -o <file> : output path"
    ,"  -O : enable optimization"
    ,"  -Sc  : to Core code"
    ,"  -Sm  : to GMachine"
    ,"  -Sbn : to BF(n)"
    ,"  --bf-addr n : use n byte for pointer arithmetic"
    ,"  --debug : include detailed error message (this will make the program a LOT larger)"
    ,""
    ,"examples:"
    ,"  hs2bf --make path/to/App.hs -o app : compile App.hs to bf"
    ,"  hs2bf --run Main -Sm : compile module Main to GMachine code and interpret it"
    ]





analyzeName :: String -> (String,Front.ModuleEnv)
analyzeName n=(takeBaseName n,Front.ModuleEnv [dirPrefix++takeDirectory n,"./test"])
    where dirPrefix=if isAbsolute n then "" else "./"





