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

-- | Statement set of SAM.
--
-- Choice between 'Memory' and 'Locate'
--
-- * 'Memory' is for local operation(in a frame), and you can expect it to be heavily optimzied.
--  (Why not use 'Locate' manually? - special register optimization is possible for 'Memory')
--
-- * 'Locate' causes permanent change, and should be used for moving between frames
--  by not-predetermined amount.
--
-- * So in principle, you should minimize use of 'Locate', and use 'Memory' instead.
data Stmt
    =While Pointer [Stmt]
    |Alloc RegName
    |Delete RegName
    |Inline ProcName [RegName]
    |Dispatch Pointer [(Int,[Stmt])]
    |Bank Region
    |Val Pointer Int
    |Move Pointer [Pointer]
    |Locate Int -- ^ ptr+=n
    |Clear Pointer -- ^ treat as a syntax sugar of Move p []
    deriving(Show)

data Pointer
    =Register RegName
    |Memory Int

instance Show Pointer where
    show (Register x)=x
    show (Memory n)
        |n==0 = "$"
        |n>0  = "$+"++show n
        |n<0  = "$"++show n

type Region=String
type ProcName=String
type RegName=String




pprint :: SAM -> String
pprint (SAM rs ps)=compileSB 0 [pre,SNewline,SNewline,procs]
    where
        pre=SBlock $ intersperse SSpace $ map SPrim rs
        procs=SBlock $ intersperse SNewline $ map pprintSP ps

pprintSP :: SProc -> StrBlock
pprintSP (SProc name reg args st)=SBlock [def,SIndent,SNewline,pprintStmts st,SNewline]
    where
        def=SBlock $ [SPrim "pr",SSpace,SPrim name,SPrim "@",SPrim reg]++darg
        darg|null args = []
            |otherwise = SPrim "/":intersperse SSpace (map SPrim args)

pprintStmts :: [Stmt] -> StrBlock
pprintStmts=SBlock . intersperse SNewline . map pprintStmt

pprintStmt :: Stmt -> StrBlock
pprintStmt (Dispatch ptr cs)=SBlock [t,b]
    where
        t=SBlock [SPrim "dispatch",SSpace,SPrim $ show ptr]
        b=SBlock $ [SIndent,SNewline]++intersperse SNewline (map pprintCase cs)
pprintStmt (While ptr ss)=SBlock [t,b]
    where
        t=SBlock [SPrim "while",SSpace,SPrim $ show ptr]
        b=SBlock [SIndent,SNewline,pprintStmts ss]
pprintStmt (Bank to)=SBlock [SPrim "bank",SSpace,SPrim to]
pprintStmt (Val p n)=SBlock [SPrim "val",SSpace,SPrim $ show p,SSpace,SPrim $ show n]
pprintStmt (Alloc n)=SBlock [SPrim "alloc",SSpace,SPrim n]
pprintStmt (Delete n)=SBlock [SPrim "delete",SSpace,SPrim n]
pprintStmt (Move d ss)=SBlock $ [SPrim "move",SSpace]++intersperse SSpace (map (SPrim . show) $ d:ss)
pprintStmt (Locate n)=SBlock [SPrim "locate",SSpace,SPrim $ show n]
pprintStmt (Inline n rs)=SBlock $ intersperse SSpace $ SPrim "inline":map SPrim (n:rs)
pprintStmt (Clear r)=SBlock [SPrim "clear",SSpace,SPrim $ show r]
-- pprintStmt x=error $ "pprintStmt:"++show x


pprintCase :: (Int,[Stmt]) -> StrBlock
pprintCase (n,ss)=SBlock [SPrim $ show n,SIndent,SNewline,pprintStmts ss]

