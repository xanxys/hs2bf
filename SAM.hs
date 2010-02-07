-- | Sequential Access Machine
--
-- This language makes implementation of various features easier by providing common C-like syntax.
--
-- Later this will be converted to very abstract graph representation and heavy optimization is
-- applied there (rule-based, mathematically-sound). It will be directly converted to BF.
--
-- This is the last language where direct debugging is possible.
--
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
--
-- Multi-byte support direction:
--
-- * multiplication etc. is supported in this layer (manually)
--
-- * 'Val' 'Dispatch' 'Clear' 'While' 'Alloc' 'Delete' 'Move' should be expanded by a new 'Pointer'
--
-- * Difference from Integer support in Prelude: fixed size
module SAM where
import Control.Arrow
import Control.Monad
import Control.Monad.State
import Data.Array.IO
import Data.Char
import Data.List
import Data.Maybe
import qualified Data.Map as M
import Data.Word


import Util
import Brainfuck


compile :: SAM -> Process BF
compile x=return undefined


-- | 
-- * Register dependency analysis
--
-- * Memory and register allocation
--
-- * Access pattern optimization
--
-- * 
simplify :: SAM -> SAM
simplify=undefined



-- | Sequential Access Machine
data SAM=SAM [Region] [SProc] deriving(Show)

data SProc=SProc ProcName Region [RegName] [Stmt] deriving(Show)

-- | Statement set of SAM.
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



data SAMInternal=SAMInternal Int [(String,FlatMemory)] [(String,Word8)]
type SAMS=State SAMInternal


-- | TODO: use faster algorithm
flatten :: SAM -> SAM
flatten (SAM rs ps)=SAM rs [flattenProc m (m M.! "^")]
    where
        m=M.fromList $ zip (map procName ps) ps


flattenProc :: M.Map ProcName SProc -> SProc -> SProc
flattenProc m proc@(SProc n reg rs ss)
    |any expandable ss = flattenProc m $ SProc n reg rs $ concatMap f ss
    |otherwise         = proc
    where
        f (Inline n ss)=expandProc ss $ M.findWithDefault (error $ "flattenProc:unknown proc "++n) n m
        f (While p ss)=[While p $ concatMap f ss]
        f (Dispatch p cs)=[Dispatch p $ map (second $ concatMap f) cs]
        f s=[s]

        expandable (Inline _ _)=True
        expandable (While _ ss)=any expandable ss
        expandable (Dispatch _ cs)=any (any expandable . snd) cs
        expandable _=False



expandProc :: [RegName] -> SProc -> [Stmt]
expandProc rs (SProc name reg rs' ss)
    |length rs/=length rs' = error $ "expandProc: arity error in "++name
    |otherwise = map (replaceStmt t) ss
    where t=M.fromList $ zipWith (\s d->(d,s++"/"++d)) rs rs'


-- | Apply register name transformation. Only valid under correct scoping.
replaceStmt :: M.Map RegName RegName -> Stmt -> Stmt
replaceStmt m (While ptr ss)=While (replacePtr m ptr) $ map (replaceStmt m) ss
replaceStmt m (Dispatch ptr cs)=Dispatch (replacePtr m ptr) $ map (second (map $ replaceStmt m)) cs
replaceStmt m (Val p n)=Val (replacePtr m p) n
replaceStmt m (Alloc n)=Alloc $ M.findWithDefault n n m
replaceStmt m (Delete n)=Delete $ M.findWithDefault n n m
replaceStmt m (Clear p)=Clear $ replacePtr m p
replaceStmt m (Move p ps)=Move (replacePtr m p) (map (replacePtr m) ps)
replaceStmt m (Inline n ss)=Inline n $ map (\x->M.findWithDefault x x m) ss
replaceStmt _ s=s

replacePtr :: M.Map RegName RegName -> Pointer -> Pointer
replacePtr m (Register x)=Register $ M.findWithDefault x x m
replacePtr _ p=p

procName :: SProc -> String
procName (SProc x _ _ _)=x
        


