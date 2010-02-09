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
import System.Environment
import System.FilePath.Posix

import Util
import qualified Front
import qualified Core
import qualified GMachine
import qualified SAM
import qualified SCGR
import qualified Brainfuck


main=execCommand =<< liftM parseArgs getArgs

-- | Complete description of /hs2bf/ behavior
data Command
    =ShowMessage String
    |Interpret Option String
    |Compile Option String

data Language
    =LangCore String
    |LangGMachine
    |LangSAM String
    |LangBF
    deriving(Show,Eq,Ord)

-- | All /global options/
data Option=Option
    {addrSpace :: Int
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
parseOption []=Option{addrSpace=2,verbose=True,debug=False,tolang=LangBF}
parseOption (term:xs)=case term of
    '-':'S':'c':xs -> o{tolang=LangCore xs}
    "-Sg" -> o{tolang=LangGMachine}
    '-':'S':'s':xs -> o{tolang=LangSAM xs}
    "-Sb" -> o{tolang=LangBF}
    _ -> error $ "unknown option:"++term
    where o=parseOption xs





execCommand :: Command -> IO ()
execCommand (ShowMessage x)=putStr x

execCommand (Interpret opt from)=do
    let (mod,env)=analyzeName from
    xs<-Front.collectModules env mod
    case tolang opt of
        LangCore _ -> error "Interpretation of Core is not supported"
        LangGMachine -> evalWith GMachine.interpretGM $ runProcess $ xs >>= Front.compile >>= Core.compile
        LangSAM _ -> error "Interpretation of SAM is not supported"
        LangBF -> evalWith Brainfuck.interpretBF $ runProcess $ xs >>= Front.compile >>= Core.compile >>=
                            GMachine.compile >>= SAM.simplify >>= SAM.compile
    where
        evalWith :: (a->IO ()) -> Either [CompileError] a -> IO ()
        evalWith f=either (putStr . unlines . map show) f

execCommand (Compile opt from)=do
    let (mod,env)=analyzeName from
    xs<-Front.collectModules env mod
    let core=xs >>= Front.compile
        gm  =core >>= Core.compile
        sam =gm   >>= GMachine.compile
        sam'=sam  >>= SAM.simplify
        bf  =sam' >>= SAM.compile
    case tolang opt of
        LangCore _   -> capProcess core Core.pprintCoreP
        LangGMachine -> capProcess gm GMachine.pprintGM
        LangSAM ""   -> capProcess sam SAM.pprint
        LangSAM "f"  -> capProcess sam' SAM.pprint
        LangBF       -> capProcess bf Brainfuck.pprint
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
    ,"  --run <module> <option>*: interpret <module>"
    ,"  --make <module> <option>*: compile <module>"
    ,""
    ,"option:"
    ,"  -o <file> : output path"
    ,"  -Sc : to Core code"
    ,"  -Sm : to GMachine"
    ,"  -Ss : to SAM"
    ,"  -Sg : to SCGR"
    ,"  -Sb : to BF"
    ,"  --addr n : use n byte for pointer arithmetic"
    ,"  --debug : include detailed error message (this will make the program a LOT larger)"
    ,""
    ,"examples:"
    ,"  hs2bf --make path/to/App.hs -o app : compile App.hs to bf"
    ,"  hs2bf --run Main -Sm : compile module Main to GMachine code and interpret it"
    ]





analyzeName :: String -> (String,Front.ModuleEnv)
analyzeName n=(takeBaseName n,Front.ModuleEnv [dirPrefix++takeDirectory n,"./test"])
    where dirPrefix=if isAbsolute n then "" else "./"





