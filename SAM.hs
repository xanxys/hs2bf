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
import qualified Data.Set as S
import Data.Word

import Util
import SCGR


compile :: SAM -> Process SCGR
compile x=return undefined


-- | 
-- * Register dependency analysis
--
-- * Memory and register allocation
--
-- * Access pattern optimization
--
-- * 
simplify :: SAM -> Process SAM
simplify s@(SAM _ procs)
    |null errors = return $ flatten s
    |otherwise   = throwError $ map f errors
    where
        f (pos,msg)=CompileErrorN "SAM->SAM" msg pos
        errors=snd $ runNMR $ mapM_ checkProc procs




-- | Sequential Access Machine
data SAM=SAM [Region] [SProc] deriving(Show)

data SProc=SProc ProcName [RegName] [Stmt] deriving(Show)

-- | Statement set of SAM.
--
-- Operations with 'RegName' in their arguments changes scope
data Stmt
    =Locate Int -- ^ ptr+=n
    |Alloc RegName
    |Delete RegName
    |Dispatch RegName [(Int,[Stmt])]
    -- ^ in cases, RegName will be out of scope. This instruction is erratic in many ways...
    --  Get rid of it ASAP! (1. Come up with new instruction, 2. expand to while on the fly)
    |Inline ProcName [RegName]
    |Clear Pointer -- ^ treat as a syntax sugar of Move p []
    |Move Pointer [Pointer]
    |Val Pointer Int
    |While Pointer [Stmt]
    deriving(Show)

data Pointer
    =Register RegName
    |Memory Region Int

instance Show Pointer where
    show (Register x)=x
    show (Memory region n)
        |n==0 = "$"++region
        |n>0  = "$"++region++"+"++show n
        |n<0  = "$"++region++show n

type Region=String
type ProcName=String
type RegName=String




pprint :: SAM -> String
pprint (SAM rs ps)=compileSB $ Pack [Line $ Line pre,procs]
    where
        pre=Span $ map Prim rs
        procs=Pack $ map pprintSP ps

pprintSP :: SProc -> StrBlock
pprintSP (SProc name args st)=Line $ Pack [def,Indent $ Pack $ map pprintStmt st]
    where
        def=Line $ Span [Prim "pr",Pack $ Prim name:darg]
        darg|null args = []
            |otherwise = [Prim "/",Span $ map Prim args]

pprintStmt :: Stmt -> StrBlock
pprintStmt (Dispatch n cs)=Pack [t,Indent b]
    where
        t=Line $ Span [Prim "dispatch",Prim n]
        b=Pack $ map pprintCase cs
pprintStmt (While ptr ss)=Pack [t,Indent b]
    where
        t=Line $ Span [Prim "while",Prim $ show ptr]
        b=Pack $ map pprintStmt ss
pprintStmt (Val p n)=Line $ Span [Prim "val",Prim $ show p,Prim $ show n]
pprintStmt (Alloc n)=Line $ Span [Prim "alloc",Prim n]
pprintStmt (Delete n)=Line $ Span [Prim "delete",Prim n]
pprintStmt (Move d ss)=Line $ Span $ Prim "move":map (Prim . show) (d:ss)
pprintStmt (Locate n)=Line $ Span [Prim "locate",Prim $ show n]
pprintStmt (Inline n rs)=Line $ Span $ map Prim ("inline":n:rs)
pprintStmt (Clear r)=Line $ Span [Prim "clear",Prim $ show r]
-- pprintStmt x=error $ "pprintStmt:"++show x


pprintCase :: (Int,[Stmt]) -> StrBlock
pprintCase (n,ss)=Pack [Line $ Prim $ show n,Indent $ Pack $ map pprintStmt ss]



data SAMInternal=SAMInternal Int [(String,FlatMemory)] [(String,Word8)]
type SAMS=State SAMInternal


-- | TODO: use faster algorithm
flatten :: SAM -> SAM
flatten (SAM rs ps)=SAM rs [flattenProc m (m M.! "^")]
    where
        m=M.fromList $ zip (map procName ps) ps


flattenProc :: M.Map ProcName SProc -> SProc -> SProc
flattenProc m proc@(SProc n rs ss)
    |any expandable ss = flattenProc m $ SProc n rs $ concatMap f ss
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
expandProc rs_parent (SProc name rs_child ss)
    |length rs_parent/=length rs_child = error $ "expandProc: arity error in "++name
    |otherwise = map (replaceStmt t) ss
    where
        pairs=filter (uncurry (/=)) $ zip rs_child rs_parent
        t=M.fromList $ concatMap (\(c,p)->[(c,p),(p,c++"/")]) pairs


-- | Apply register name transformation. Only valid under correct scoping.
replaceStmt :: M.Map RegName RegName -> Stmt -> Stmt
replaceStmt m (While ptr ss)=While (replacePtr m ptr) $ map (replaceStmt m) ss
replaceStmt m (Dispatch n cs)=Dispatch (replaceReg m n) $ map (second (map $ replaceStmt m)) cs
replaceStmt m (Val p n)=Val (replacePtr m p) n
replaceStmt m (Alloc n)=Alloc $ M.findWithDefault n n m
replaceStmt m (Delete n)=Delete $ M.findWithDefault n n m
replaceStmt m (Clear p)=Clear $ replacePtr m p
replaceStmt m (Move p ps)=Move (replacePtr m p) (map (replacePtr m) ps)
replaceStmt m (Inline n ss)=Inline n $ map (replaceReg m) ss
replaceStmt _ s=s

replaceReg :: M.Map RegName RegName -> RegName -> RegName
replaceReg m x=M.findWithDefault x x m

replacePtr :: M.Map RegName RegName -> Pointer -> Pointer
replacePtr m (Register x)=Register $ M.findWithDefault x x m
replacePtr _ p=p

procName :: SProc -> String
procName (SProc x _ _)=x





type NMRE a=NMR String String a


-- | Find static erros in a 'SProc'.
-- 
-- * unknown registers
--
-- * unmatched register and bank in 'While' and 'Dispatch'
--
-- * modification of flag register in 'Dispatch'
--
-- All of this is handled via scope analysis, but done differently from conventional techniques.
--
-- Rather than tracking "bound variables", see each statement as BV-set transformer.
--
-- * Alloc makes adding transformer
--
-- * Delete makes removing transformer
--
-- * Transformer merge (sequential,parallel) is defined, and whole proc must be id.
checkProc :: SProc -> NMRE ()
checkProc (SProc name args ss)=within ("proc "++name) $ do
    let rs=S.fromList args
    when (S.size rs/=length args) $ report "duplicate arguments"
    rs'<-checkStmt ss rs
    when (rs/=rs') $ report $ "leaking registers: "++unwords (S.toList $ rs' S.\\ rs)


checkStmt :: [Stmt] -> S.Set RegName -> NMRE (S.Set RegName)
checkStmt [] rs=return rs
checkStmt ((While ptr ss):xs) rs=do
    within "while flag" $ checkPointer ptr rs
    rs'<-within "while body" $ checkStmt ss rs
    when (rs/=rs') $ within "while" $ report $ "leaking registers: "++unwords (S.toList $ rs' S.\\ rs)
    checkStmt xs rs
checkStmt ((Dispatch n cs):xs) rs=do
    unless (S.member n rs) $ within "dispatch header" $ report $ "unknown register:"++show n
    let rsBody=S.delete n rs
    rss<-mapM (\(n,ss)->within ("dispatch body "++show n) $ checkStmt ss rsBody) cs
    let probs=filter ((/=rsBody) . snd) $ zip (map fst cs) rss
    mapM_ (\(n,rsB)->within ("end of dispatch body "++show n) $ report $ "leaking registers:"++unwords (S.toList $ rsB S.\\ rsBody)) probs 
    checkStmt xs rs
checkStmt ((Alloc n):xs) rs=do
    when (S.member n rs) $ report $ "duplicated allocation of "++n
    checkStmt xs $ S.insert n rs
checkStmt ((Delete n):xs) rs=do
    unless (S.member n rs) $ report $ "deleting unallocated register "++n
    checkStmt xs $ S.delete n rs
checkStmt ((Move p ps):xs) rs=mapM_ (\x->within "move" $ checkPointer x rs) (p:ps) >> checkStmt xs rs
checkStmt ((Val p _):xs) rs=within "val" (checkPointer p rs) >> checkStmt xs rs
checkStmt ((Clear p):xs) rs=within "clear" (checkPointer p rs) >> checkStmt xs rs
checkStmt ((Inline name ns):xs) rs=do
    let s=S.fromList ns
    unless (s `S.isSubsetOf` rs) $ within ("inline "++name) $ report $ "unknown registers: " ++unwords (S.toList $s S.\\ rs)
    checkStmt xs rs
checkStmt (_:xs) rs=checkStmt xs rs


checkPointer :: Pointer -> S.Set RegName -> NMRE ()
checkPointer (Register x) rs=unless (S.member x rs) $ within "pointer" $ report $ "unknown register: "++x
checkPointer _ rs=return ()





