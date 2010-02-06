module SAM where
import Control.Monad
import Data.Array.IO
import Data.Char
import Data.List
import Data.Word

import Util
import Brainfuck



compile :: SAM -> Process BFM
compile x=return undefined



-- | Sequential Access Machine
data SAM=SAM [Region] [SProc] deriving(Show)

data SProc=SProc ProcName Region [RegName] [Stmt] deriving(Show)

data Stmt
    =While Pointer [Stmt]
    |Alloc RegName
    |Delete RegName
    |Inline ProcName [RegName]
    |Dispatch Pointer [(Int,[Stmt])]
    |Halt
    |Bank Region Region
    |Ptr Int
    |Clear Pointer
    |Val Pointer Int
    |Move Pointer [Pointer]
    deriving(Show)

data Pointer
    =Register RegName
    |Memory

instance Show Pointer where
    show (Register x)=x
    show Memory="$"

type Region=String
type ProcName=String
type RegName=String




pprint :: SAM -> String
pprint (SAM rs ps)=compileSB 0 [pre,SNewline,procs]
    where
        pre=SBlock $ intersperse SSpace $ map SPrim rs
        procs=SBlock $ map pprintSP ps

pprintSP :: SProc -> StrBlock
pprintSP (SProc name reg args st)=SBlock [def,SIndent,SNewline,SBlock $ map pprintStmt st,SNewline]
    where
        def=SBlock $ [SPrim "pr",SSpace,SPrim name,SPrim "@",SPrim reg]++darg
        darg|null args = []
            |otherwise = SPrim "/":intersperse SSpace (map SPrim args)

pprintStmt :: Stmt -> StrBlock
pprintStmt (While ptr ss)=SBlock [t,b]
    where
        t=SBlock [SPrim "while",SSpace,SPrim $ show ptr]
        b=SBlock $ SIndent:SNewline:intersperse SNewline (map pprintStmt ss)
pprintStmt (Ptr n)=SBlock [SPrim "ptr",SSpace,SPrim $ show n]
pprintStmt (Bank fr to)=SBlock [SPrim "bank",SSpace,SPrim fr,SSpace,SPrim to]



