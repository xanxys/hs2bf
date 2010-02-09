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
import Numeric
import Text.Printf

import Util
import SCGR
import Brainfuck


compile :: SAM -> Process SCGR
compile (SAM _ [SProc _ [] ss])=return $ BF $ soptBF $ concatMap compileS ss

soptBF []=[]
soptBF xs=case head xs of
    BFPInc -> sopAux 0 xs
    BFPDec -> sopAux 0 xs
    BFVInc -> sovAux 0 xs
    BFVDec -> sovAux 0 xs
    BFLoop s -> BFLoop (soptBF s):xs'
    _ -> BFInput:xs'
    where xs'=soptBF $ tail xs

sopAux n (BFPInc:xs)=sopAux (n+1) xs
sopAux n (BFPDec:xs)=sopAux (n-1) xs
sopAux n xs=dP n++soptBF xs

sovAux n (BFVInc:xs)=sovAux (n+1) xs
sovAux n (BFVDec:xs)=sovAux (n-1) xs
sovAux n xs=dV n++soptBF xs

compileS (Move p ps)=
    (concatMap (\p->compileS $ While p [Val p (-1)]) ps)++
    (compileS $ While p $ Val p (-1):map (flip Val 1) ps)
compileS (While (Memory _ d) ss)=concat
    [dP d
    ,[BFLoop $ concat [dP (negate d),concatMap compileS ss,dP d]]
    ,dP (negate d)]
compileS (Val (Memory _ d) v)=concat [dP d,dV v,dP $ negate d]
compileS (Locate d)=dP d

dP x=replicateZ x BFPDec BFPInc
dV x=replicateZ x BFVDec BFVInc


replicateZ x m p
    |x==0 = []
    |x>0  = replicate x p
    |x<0  = replicate (negate x) m



-- | Apply this before 'SAM.compile'
--
-- * 'flatten': expand all inline calls
--
-- * 'desugar': 'Dispatch' -> 'While' 'Clear' -> 'Move'
--     (don't expand 'Move' here, since they are good for later optimization)
--
-- * 'foldMemory': allocate registers
simplify :: SAM -> Process SAM
simplify s=
    checkSAM "SAM" s       >>= return . flatten "^" >>=
    checkSAM "SAM:flat"    >>= return . desugar >>=
    checkSAM "SAM:desugar" >>= return . allocateRegister >>=
    checkSAM "SAM:ralloc"  >>= return . foldMemory >>=
    checkSAM "SAM:folded"


-- | no register access
foldMemory :: SAM -> SAM
foldMemory (SAM rs [SProc name [] ss])=SAM [""] [SProc name [] $ map (foldMS (length rs) rs) ss]

foldMS n m (Move p ps)=Move (foldMP n m p) (map (foldMP n m) ps)
foldMS n m (While p ss)=While (foldMP n m p) (map (foldMS n m) ss)
foldMS n m (Val p d)=Val (foldMP n m p) d
foldMS n m (Locate d)=Locate $ n*d

foldMP n m (Memory r x)=Memory "" $ (fromJust $ elemIndex r m)+x*n


-- | /very bad/ register allocator
allocateRegister :: SAM -> SAM
allocateRegister (SAM rs [SProc name [] ss])
    |rs' `eqRS` [] = SAM (rs++["R"]) [SProc name [] $ concat sss]
    |otherwise     = error $ "allocateRegister: leaking register: "++show rs'
    where (rs',sss)=mapAccumL allocateRS [] ss

allocateRS :: [Maybe RegName] -> Stmt -> ([Maybe RegName],[Stmt])
allocateRS rs (Alloc r)=case elemIndex Nothing rs of
    Nothing -> (rs++[Just r],[Move (Memory "R" $ length rs) []])
    Just ix -> (mapAt ix (const $ Just r) rs,[Move (Memory "R" ix) []])
allocateRS rs (Delete r)=case elemIndex (Just r) rs of
    Just ix -> (mapAt ix (const Nothing) rs,[Move (Memory "R" ix) []])
    Nothing -> error $ "allocateRS: deleting unknown register: "++r
allocateRS rs (Move p ps)=(rs,[Move (allocateRP rs p) (map (allocateRP rs) ps)])
allocateRS rs (While p ss)
    |eqRS rs rs' = (rs,[While (allocateRP rs p) $ concat sss])
    |otherwise   = error "allocateRS: unmatched register scope in while"
    where (rs',sss)=mapAccumL allocateRS rs ss
allocateRS rs (Val p d)=(rs,[Val (allocateRP rs p) d])
allocateRS rs (Locate d)=(rs,mv++[Locate d])
    where
        mv=map (gen . fst) $ filter (isJust . snd) $ zip [0..] rs
        gen ix=Move (Memory "R" ix) [Memory "R" $ ix+d]
        
        
eqRS :: [Maybe RegName] -> [Maybe RegName] -> Bool
eqRS [] []=True
eqRS (Nothing:xs) []=eqRS xs []
eqRS [] (Nothing:ys)=eqRS [] ys
eqRS (x:xs) (y:ys)=(x==y) && (xs `eqRS` ys)
eqRS _ _=False

                


allocateRP :: [Maybe RegName] -> Pointer -> Pointer
allocateRP rs (Memory x d)=Memory x d
allocateRP rs (Register r)
    =maybe (error $ "allocateRP: non-allocated register: "++r) (Memory "R") $ elemIndex (Just r) rs




desugar :: SAM -> SAM
desugar (SAM rs [SProc name [] ss])=SAM rs [SProc name [] ss']
    where
        ss'=[Alloc "_dt"]++concatMap desugarStmt ss++[Delete "_dt"]

desugarStmt :: Stmt -> [Stmt]
desugarStmt (Dispatch r cs)=concatMap desugarStmt $ expandDispatch r $ sortBy (comparing fst) cs
desugarStmt (While ptr ss)=[While ptr $ concatMap desugarStmt ss]
desugarStmt (Clear ptr)=[Move ptr []]
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

procName :: SProc -> ProcName
procName (SProc name _ _)=name

-- | Statement set of SAM.
--
-- Operations with 'RegName' in their arguments changes scope
data Stmt
    =Locate Int -- ^ ptr+=n
    |Alloc RegName
    |Delete RegName
    |Dispatch RegName [(Int,[Stmt])] -- ^ in case alts, given RegName will be out of scope. This instruction is erratic in many ways...
    |Inline ProcName [RegName]
    |Clear Pointer -- ^ syntax sugar of Move p []
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
                  Nothing  -> n++"/"++reg
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



-- | Interpreter of 'SAM', usable for all phases.
interpret :: SAM -> IO ()
interpret s@(SAM rs procs)=do
    runProcessWithIO (const $ return ()) $ checkSAM "SAMi" s
    let
        ptb0=M.fromList $ map (procName &&& id) procs
        mtb0=(M.fromList $ zip rs $ repeat minit)
        st0=SAMInternal ptb0 mtb0 M.empty 0
    
    evalStateT (enterProc "^" []) st0

data SAMInternal=SAMInternal
    {procTable :: M.Map ProcName SProc
    ,memTable :: MemTable
    ,regTable :: RegTable
    ,pointer :: Int
    }

type MemTable=M.Map Region FlatMemory
type RegTable=M.Map ProcName (M.Map RegName Word8,M.Map RegName (ProcName,RegName))

type SAMST=StateT SAMInternal


enterProc :: ProcName -> [(ProcName,RegName)] -> SAMST IO ()
enterProc name args=do
    liftIO $ putStrLn $ "entering:"++name
    dumpRegisters
    dumpMemory
    
    ptb<-liftM procTable get
    rtb<-liftM regTable get
    let SProc _ rs ss=M.findWithDefault (error $ "SAMi: procedure not found: "++name) name ptb
    when (length rs/=length args) $ error $ "SAMi: procedure arity error: "++show (name,rs,args) 
    when (M.member name rtb) $ error $ "SAMi: re-entring to precedure: "++name
    
    let rtb'=M.insert name (M.empty,M.fromList $ zipWith (\org to->(to,uncurry (reduceReg rtb) org)) args rs) rtb
    modify (\x->x{regTable=rtb'})
--    mapM_ (\x->execStmt name x >> dumpRegisters >> dumpMemory >> liftIO (putStrLn "")) ss
    mapM_ (execStmt name) ss
    modify (\x->x{regTable=M.delete name $ regTable x})

dumpMemory :: SAMST IO ()
dumpMemory=do
    t<-liftM memTable get
    p<-liftM pointer get
    let maxAddr=max 0 $ maximum (map msize $ M.elems t)-1
        ss=map (\x->dumpMemoryBetween p t (x*w,(x+1)*w-1)) [0..maxAddr `div` w]
    liftIO $ putStr $ unlines ss
    where w=16

dumpMemoryBetween :: Int -> MemTable -> (Int,Int) -> String
dumpMemoryBetween p t (a0,a1)=unlines $ map dumpKey ks
    where
        ks=M.keys t
        head=maximum $ map length ks
        dumpKey k=printf ("%"++show head++"s|") k++dump (t M.! k)
        dump fm=unwords $ map (\x->showAddr x $ mread fm x) [a0..a1]
        showAddr a v=(if a==p then ">" else " ")++(showHex v "")

dumpRegisters :: SAMST IO ()
dumpRegisters=do
    r<-liftM regTable get
    let ss=map (uncurry dumpRegisterP) $ M.assocs r
    liftIO $ putStr $ concat ss

dumpRegisterP :: ProcName -> (M.Map RegName Word8,M.Map RegName (ProcName,RegName)) -> String
dumpRegisterP proc (m0,m1)
    |null rs = ""
    |otherwise = unlines $ ("in "++proc++":"):rs
    where
        rs=(map (\(n,v)->"  "++n++": "++showHex v "") $ M.assocs m0)++
           (map (\(n,a)->"  "++n++" -> "++show a) $ M.assocs m1)

    
    

execStmt p (Alloc r)=modifyRT $ M.adjust (first $ M.insert r 0) p
execStmt p (Delete r)=modifyRT $ M.adjust (first $ M.delete r) p
execStmt p (Inline n rs)=enterProc n (zip (repeat p) rs)
execStmt p (Val ptr d)=liftM (+fromIntegral d) (readPtr p ptr) >>= writePtr p ptr
execStmt p s0@(While ptr ss)=do
    x<-readPtr p ptr
    when (x/=0) $ mapM_ (execStmt p) ss >> execStmt p s0
execStmt p (Move ptr ptrs)=forM (ptr:ptrs) (readPtr p) >>= zipWithM_ (\ptr x->writePtr p ptr x) (ptr:ptrs) . f
    where f (x:xs)=0:repeat x
execStmt p (Locate d)=modifyPointer (+d)
execStmt p (Dispatch r cs)=do
    x<-readPtr p (Register r)
    let caluse=lookup (fromIntegral x) cs
    maybe (error $ "SAMi: unhandled value in dispatch: "++show (x,p,r)) (mapM_ $ execStmt p) caluse
execStmt p (Clear ptr)=writePtr p ptr 0
    
    
    
    
readPtr :: Monad m => ProcName -> Pointer -> SAMST m Word8
readPtr p (Memory r d)=do
    dp<-liftM pointer get
    when (dp+d<0) $ error $ "readPtr: invalid op:"++show (p,r,dp,d)
    liftM (flip mread (dp+d) . (M.! r) . memTable) get
readPtr p (Register r)=liftM (flip (flip readReg p) r . regTable) get


writePtr :: Monad m => ProcName -> Pointer -> Word8 -> SAMST m ()
writePtr p (Memory r d) x=do
    dp<-liftM pointer get
    when (dp+d<0) $ error $ "writePtr: invalid op:"++show (p,r,dp,d)
    modifyMT $ M.adjust (flip (flip mwrite (dp+d)) x) r
writePtr p (Register r) x=modifyRT (\t->writeReg t p r x)




readReg :: RegTable -> ProcName -> RegName -> Word8
readReg t p r=(fst (t M.! p')) M.! r'
    where (p',r')=reduceReg t p r

writeReg :: RegTable -> ProcName -> RegName -> Word8 -> RegTable
writeReg t p r x=M.adjust (first $ M.insert r' x) p' t
    where (p',r')=reduceReg t p r


reduceReg :: RegTable -> ProcName -> RegName -> (ProcName,RegName)
reduceReg t p r
    |M.member r org = (p,r)
    |otherwise      = alias M.! r
    where (org,alias)=t M.! p



modifyRT :: Monad m => (RegTable -> RegTable) -> SAMST m ()
modifyRT f=modify $ \x->x{regTable=f $ regTable x}

modifyMT :: Monad m => (MemTable -> MemTable) -> SAMST m ()
modifyMT f=modify $ \x->x{memTable=f $ memTable x}

modifyPointer :: Monad m => (Int -> Int) -> SAMST m ()
modifyPointer f=modify $ \x->x{pointer=g $ pointer x}
    where g x=let y=f x in if x<0 then error $ "modifyPointer: invalid pos: "++show y else y


