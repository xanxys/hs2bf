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
import Data.Char
import Data.Either
import Data.Graph
import Data.List
import Data.Maybe
import Data.Ord
import Data.Word
import qualified Data.Map as M
import qualified Data.Set as S

import Util
import SCGR


compile :: SAM -> Process SCGR
compile x=return undefined


foldMemory :: SAM -> Process SAM
foldMemory (SAM rs procs)=return $ SAM rs procs

-- | Apply this before 'SAM.compile'
--
-- * 'flatten': expand all inline calls
--
-- * 'desugar': 'Dispatch' -> 'While'
--     (don't expand 'Clear' or 'Move' here, since they are good for later optimization)
simplify :: SAM -> Process SAM
simplify s=
    checkSAM "SAM" s >>= return . flatten "^" >>=
    checkSAM "SAM:flattened" >>= return . desugar >>=
    checkSAM "SAM:desugared"

desugar :: SAM -> SAM
desugar (SAM rs [SProc name [] ss])=SAM rs [SProc name [] ss']
    where
        ss'=[Alloc "_dt"]++concatMap desugarStmt ss++[Delete "_dt"]

desugarStmt :: Stmt -> [Stmt]
desugarStmt (Dispatch r cs)=concatMap desugarStmt $ expandDispatch r $ sortBy (comparing fst) cs
desugarStmt (While ptr ss)=[While ptr $ concatMap desugarStmt ss]
desugarStmt s=[s]

-- | Case numbers must be sorted in ascending order.
expandDispatch r []=[]
expandDispatch r ((n0,e0):cs)=
    [Clear (Register "_dt")
    ,Val (Register r) (negate $ n0)
    ,While (Register r) $
        expandDispatch r (map (\(n,e)->(n-n0,e)) cs)++
        [Clear (Register "_dt")
        ,Val (Register "_dt") 1
        ]
    ,While (Register "_dt") $
        e0++
        [Clear (Register "_dt")]
    ]



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
    -- ^ in case alts, given RegName will be out of scope. This instruction is erratic in many ways...
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


-- | Flatten procedures with given root.
flatten :: ProcName -> SAM -> SAM
flatten root (SAM rs ps)
    |not $ null cycles = error $ "flatten: dependency cycles:\n"++unlines (map unwords cycles)
    |otherwise         = SAM rs [m2p root $ foldl expandProc (ps2m ps) vs]
    where
        (cycles,vs)=partitionEithers $ map f $ stronglyConnComp $ map procNode ps
        f (AcyclicSCC x)=Right x
        f (CyclicSCC xs)=Left xs
    
        ps2m=M.fromList . map (\(SProc name args ss)->(name,(args,ss)))
        m2p r m=uncurry (SProc r) $ m M.! r



-- | Construct a node for procedure dependecy graph
procNode :: SProc -> (ProcName,ProcName,[ProcName])
procNode (SProc n args ss)=(n,n,S.toList $ S.unions $ map stmtDep ss)

-- | Collect 'Inline'd procedures from 'Stmt'
stmtDep :: Stmt -> S.Set ProcName
stmtDep (While _ ss)=S.unions $ map stmtDep ss
stmtDep (Dispatch _ cs)=S.unions $ map stmtDep $ concatMap snd cs
stmtDep (Inline n _)=S.singleton n
stmtDep _=S.empty

-- | Expand the given proc in the map non-recursively.
expandProc :: M.Map ProcName ([RegName],[Stmt]) -> ProcName -> M.Map ProcName ([RegName],[Stmt])
expandProc m r=M.adjust (second $ expandStmts m) r m

expandStmts :: M.Map ProcName ([RegName],[Stmt]) -> [Stmt] -> [Stmt]
expandStmts m=concatMap (expandStmt m)

expandStmt :: M.Map ProcName ([RegName],[Stmt]) -> Stmt -> [Stmt]
expandStmt m (Inline n rsP)=map (replaceStmt f) ss
    where
        (rsC,ss)=M.findWithDefault (error $ "flattenProc:unknown proc "++n) n m
        f reg=case lookup reg $ zip rsC rsP of
                  Just rsp -> rsp
                  Nothing  -> if elem reg rsP then n++"/"++reg else reg
expandStmt m (While p ss)=[While p $ expandStmts m ss]
expandStmt m (Dispatch p cs)=[Dispatch p $ map (second $ expandStmts m) cs]
expandStmt _ s=[s]


-- | Apply register name transformation.
replaceStmt :: (RegName -> RegName) -> Stmt -> Stmt
replaceStmt f (While ptr ss)=While (replacePtr f ptr) $ map (replaceStmt f) ss
replaceStmt f (Dispatch n cs)=Dispatch (f n) $ map (second (map $ replaceStmt f)) cs
replaceStmt f (Val p n)=Val (replacePtr f p) n
replaceStmt f (Alloc n)=Alloc $ f n
replaceStmt f (Delete n)=Delete $ f n
replaceStmt f (Clear p)=Clear $ replacePtr f p
replaceStmt f (Move p ps)=Move (replacePtr f p) (map (replacePtr f) ps)
replaceStmt f (Inline n ss)=error "replaceStmt: Inline: re-check expansion order"
replaceStmt _ s=s

replacePtr :: (RegName -> RegName) -> Pointer -> Pointer
replacePtr f (Register x)=Register $ f x
replacePtr _ p=p





-- | 'NRM' instance for use in 'checkProc'
type NMRE a=NMR String String a

-- | Just a wrapper of 'checkProc' for 'SAM'. No additional checks.
checkSAM :: String -> SAM -> Process SAM
checkSAM loc s@(SAM x procs)
    |null errors = return s
    |otherwise   = throwError errors
    where
        errors=map (\(pos,msg)->CompileErrorN loc msg pos) $ snd $ runNMR $ mapM_ checkProc procs


-- | Find static erros in a 'SProc'.
-- 
-- What's being done here is usual variable scope analysis. But the data dependecy graph will be a
-- DAG, not tree.
--
-- * unknown registers
--
-- * unmatched register in 'While' and 'Dispatch'
--
-- TODO:
--
-- * 'Alloc' or 'Delete' of argument registers
--
-- * modification of flag register in 'Dispatch'
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
    let integrity rsB=when (rsB/=rs) $ report $ "leaking registers:"++unwords (S.toList $ rsB S.\\ rs)
    forM_ cs (\(n,ss)->within ("dispatch clause "++show n) $ checkStmt ss rs >>= integrity)
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





