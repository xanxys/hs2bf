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
import System.IO

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
    |LangGM   String
    |LangSAM  String
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
    '-':'S':'g':xs -> o{tolang=LangGM   xs}
    '-':'S':'s':xs -> o{tolang=LangSAM  xs}
    "-Sb" -> o{tolang=LangBF}
    _ -> error $ "unknown option:"++term
    where o=parseOption xs





execCommand :: Command -> IO ()
execCommand (ShowMessage x)=putStrLn x
execCommand (Interpret opt from)=partialChain opt from $
    (error "Core interpreter is not implemented"
    ,error "Core interpreter is not implemented"
    ,f GMachine.interpret
    ,f GMachine.interpretR
    ,f SAM.interpret
    ,f SAM.interpret
    ,f Brainfuck.interpret
    )
    where
        f g=runProcessWithIO (\x->setio >> g x)
        setio=hSetBuffering stdin NoBuffering >> hSetBuffering stdout NoBuffering
execCommand (Compile opt from)=partialChain opt from $
    (f Core.pprint
    ,f Core.pprint
    ,f GMachine.pprint
    ,f GMachine.pprint
    ,f SAM.pprint
    ,f SAM.pprint
    ,f Brainfuck.pprint
    )
    where f g=runProcessWithIO (putStr . g)

partialChain opt from (c0,c1,g0,g1,s0,s1,b)=do
    let (mod,env)=analyzeName from
    xs<-Front.collectModules env mod
    let cr  =xs   >>= Front.compile
        cr' =cr   >>= Core.simplify
        gm  =cr'  >>= Core.compile
        gm' =gm   >>= GMachine.simplify
        sam =gm'  >>= GMachine.compile
        sam'=sam  >>= SAM.simplify
        bf  =sam' >>= SAM.compile
    case tolang opt of
        LangCore ""  -> c0 cr
        LangCore "s" -> c1 cr'
        LangGM  ""   -> g0 gm
        LangGM  "r"  -> g1 gm'
        LangSAM ""   -> s0 sam
        LangSAM "f"  -> s1 sam'
        LangBF       -> b  bf

version :: String
version="version 0.3"

help :: String
help=unlines $
    ["Usage: hs2bf <command>"
    ,""
    ,"command:"
    ,"  --help: show help"
    ,"  --version: show version"
    ,"  --run <module> <option>*: interpret <module>"
    ,"  --make <module> <option>*: compile <module>"
    ,""
    ,"option:"
    ,"  -o <file> : output path (stdout if omitted)"
    ,"  -Sc : to Core code"
    ,"  -Scs: to Core code (simplified)"
    ,"  -Sg : to GMachine"
    ,"  -Sgr: to GMachine (simplified)"
    ,"  -Ss : to SAM"
    ,"  -Ssf: to SAM (most simplified)"
    ,"  -Sr : to SCGR"
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


