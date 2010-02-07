-- | Create a chain based on given arguments and run it.
--
-- Overall development policy:
--
-- * If you seek /elegant/ abstraction, you will get /elephant/ abstraction.
--
-- * All intermediate-languages should be interpretable in 'IO' monad with exactly same behavior,
--   or at least have such semantics.
--
-- * Interpreters should not try to optimize, use simplest implementation while keeping the order low.
--
-- See the source of 'help' for detailed description\/specification of features.
module Main where
import Control.Monad
import Language.Haskell.Pretty
import System.Environment
import System.FilePath.Posix

import Util
import qualified Front
import qualified Core
import qualified GMachine
import qualified SAM
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
    |LangSAM
    |LangBF
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
parseOption []=Option{optimize=False,bfAddrSpace=2,verbose=True,debug=False,tolang=LangBF}
parseOption (term:xs)=case term of
    "-O"  -> o{optimize=True}
    "-Sc" -> o{tolang=LangCore}
    "-Sg" -> o{tolang=LangGMachine}
    "-Ss" -> o{tolang=LangSAM}
--    "-Sm" -> o{tolang=LangBFM}
--    "-Sk" -> o{tolang=LangBFC}
    "-Sb" -> o{tolang=LangBF}
    _ -> error $ "unknown option:"++term
    where o=parseOption xs





execCommand :: Command -> IO ()
execCommand (ShowMessage x)=putStr x

execCommand (Interpret opt from)=do
    let (mod,env)=analyzeName from
    xs<-Front.collectModules env mod
    case tolang opt of
        LangCore -> error "Interpretation of Core is not supported"
        LangGMachine -> evalWith GMachine.interpretGM $ runProcess $ xs >>= Front.compile >>= Core.compile
        LangSAM -> error "Interpretation of SAM is not supported"
--        LangBFM -> error "Interpretation of BFM is not supported"
--        LangBFC -> error "Interpretation of BFC is not supported"
        LangBF -> evalWith Brainfuck.interpretBF $ runProcess $ xs >>= Front.compile >>= Core.compile >>=
                            GMachine.compile >>= SAM.compile
    where
        evalWith :: (a->IO ()) -> Either [CompileError] a -> IO ()
        evalWith f=either (putStr . unlines . map show) f

execCommand (Compile opt from)=do
    let (mod,env)=analyzeName from
    xs<-Front.collectModules env mod
    let core=xs >>= Front.compile
        gm  =core >>= Core.compile
        sam =gm   >>= GMachine.compile >>= return . SAM.flatten
--        bfm =sam  >>= SAM.compile
--        bfc =bfm  >>= Brainfuck.compileM
        bf  =sam  >>= SAM.compile -- Brainfuck.compileC
    case tolang opt of
        LangCore     -> capProcess core Core.pprintCoreP
        LangGMachine -> capProcess gm  GMachine.pprintGM
        LangSAM      -> capProcess sam SAM.pprint
--        LangBFM      -> capProcess bfm show
--        LangBFC      -> capProcess bfc show
        LangBF       -> capProcess bf  show
    where
        capProcess pr f=outputWith f $ runProcess pr
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





