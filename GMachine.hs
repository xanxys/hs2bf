-- | GMachine
-- reference: Implementing Functional Languages: a tutorial
--
-- GC is executed every 256 allocation.
module GMachine where
import Control.Arrow
import Control.Monad
import Control.Monad.State
import Control.Monad.Identity
import Data.Ord
import Data.Char
import Data.List
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S

import Util as U hiding(Pack)
import qualified Util as U
import SRuntime
import SAM


data GFCompileFlag=GFCompileFlag
    {addrSpace :: Int -- ^ bytes
    }


-- | Compile 'GMCode's to SAM
--
-- See my blog (japanese) for overview of operational model.
--
-- Heap frame of size k with n-byte address:
--
-- * 1 B: size of this frame
--
-- * 1 B: GC tag
--
-- * k B: payload
--
-- * n B: id of this frame
-- 
-- * 1 B: size of this frame 
--
-- Heap frame of size k with n-byte address:
--
-- Is it a good idea to remove GC tag, and attach it only when GC is running?
--   (PRO:normally faster,CON:slower gcTransfer)
--
--
-- Heap payload:
--
-- You can return from anywhere on stack to origin, but not from heap.
compile :: M.Map String [GMCode] -> Process SAM
compile m
    |codeSpace>1          = error "GM->SAM: 255+ super combinator is not supported"
    |heapSpace>1          = error "GM->SAM: 2+ byte addresses are not supported"
    |M.notMember "main" m = error "GM->SAM: entry point not found"
    |otherwise            = return $ SAM (ss++hs) (library++dispatcher++procs)
    where
        t=M.fromList $ ("main",2):zip (filter (/="main") $ M.keys m) [3..]
        
        -- code generation
        library=genLibrary $ S.toList $ S.unions $ map (S.unions . map collectConArity) $ M.elems m
        procs=map (uncurry $ compileProc t) $ M.assocs m
        dispatcher=[exec $ M.assocs t]
                
        -- layout configuration
        codeSpace=ceiling $ log (fromIntegral $ M.size m+2)/log 256
        heapSpace=1
        ss=map (("S"++) . show) [0..heapSpace-1]
        hs=["Hp","Hs"]

collectConArity :: GMCode -> S.Set Int
collectConArity (Pack _ n)=S.singleton n
collectConArity (Case cs)=S.unions $ map (S.unions . map collectConArity . snd) cs
collectConArity _=S.empty



simplify :: M.Map String [GMCode] -> Process (M.Map String [GMCode])
simplify=return . M.map elimBase . elimReduce . removeLoneSC

removeLoneSC :: M.Map String [GMCode] -> M.Map String [GMCode]
removeLoneSC m=M.filterWithKey (\k _->S.member k col) m
    where col=rlscAux m S.empty (S.singleton "main")

rlscAux :: M.Map String [GMCode] -> S.Set String -> S.Set String -> S.Set String
rlscAux m col front
    |S.null front = col
    |otherwise    = rlscAux m col' (S.difference new col')
    where
        col'=S.union col front
        new=S.unions $ map (S.unions . map collectDepSC . find) $ S.toList front
        find x=M.findWithDefault (error $ "rlscAux:"++show x) x m


collectDepSC :: GMCode -> S.Set String
collectDepSC (PushSC x)=S.singleton x
collectDepSC (Case cs)=S.unions $ map (S.unions . map collectDepSC . snd) cs
collectDepSC _=S.empty


-- | Optmize away /base/ cases like following.
--
-- * Case with 1 clause
--
-- * Pop 0
--
-- * Slide 0 (in fact, successive 'Slide's form a 'Monoid')
elimBase :: [GMCode] -> [GMCode]
elimBase []=[]
elimBase (Slide 0:xs)=elimBase xs
elimBase (Slide n:Slide m:xs)=elimBase $ Slide (n+m):xs
elimBase (Case cs:xs)
    |length cs<=1 = elimBase $ (snd $ head cs)++xs
    |otherwise    = Case (map (second elimBase) cs):elimBase xs
elimBase (Pop 0:xs)=elimBase xs
elimBase (x:xs)=x:elimBase xs


-- | Separate ['GMCode'] at 'Reduce'.
elimReduce :: M.Map String [GMCode] -> M.Map String [GMCode]
elimReduce=M.fromList . concatMap f . M.assocs
    where f (n,xs)=aux n [] xs


aux :: String -> [GMCode] -> [GMCode] -> [(String,[GMCode])]
aux n cs []=[(n,reverse cs)]
aux n cs (Reduce _:xs)=(n,reverse cs++[PushSC n',Swap]):aux n' [] xs
    where n'=n++"_"
aux n cs (Case as:xs)
    |null rs   = aux n (Case as:cs) xs
    |otherwise = (n,reverse $ Case as'':cs):rs
    where
        as'=map (\(k,x)->(k,aux (n++"_d"++show k) [] $ x++xs)) as
        as''=map (second $ snd . head) as'
        rs=concatMap (tail . snd) as'
aux ns cs (x:xs)=aux ns (x:cs) xs




-- | Thin wrapper of 'compileCodeBlock'
compileProc :: M.Map String Int -> String -> [GMCode] -> SProc
compileProc m name cs=SProc ("!"++name) [] $ contWith m Origin cs []


data MPos
    =HeapA
    |StackA
    |StackT
    |Origin
    deriving(Show,Eq)

fPos :: GMCode -> MPos
fPos (PushByte _)=HeapA
fPos (PushSC _)=HeapA
fPos MkApp=HeapA
fPos (Pack _ _)=HeapA
fPos Swap=StackT
fPos (Push _)=StackA
fPos (Slide _)=StackT
fPos (PushArg _)=StackT
fPos (Case _)=StackT
fPos (UnPack _)=StackA
fPos (Update _)=StackT
fPos (Pop _)=StackT
fPos (GMachine.Alloc _)=fPos $ PushByte 0
fPos (Arith _)=StackT
fPos (UError _)=StackA -- any position will do, actually.
fPos x=error $ show x


-- requirement: HeapA
newFrame :: Int -> [Int] -> (Pointer -> [Stmt]) -> [Stmt]
newFrame tag xs post=
    [Comment $ unwords ["nf",show tag,show xs]
    ,SAM.Alloc "addr"
    ,Inline "#heapNewHp" ["addr"]
    ,Clear (Memory "Hp" $ size-2)
    ,Move (Register "addr") [Memory "Hp" $ size-2]
    ,Delete "addr"
    ,Val (Memory "Hp" 0) size
    ,Clear (Memory "Hp" 1),Val (Memory "Hp" 1) 0 -- GC tag
    ,Clear (Memory "Hp" 2),Val (Memory "Hp" 2) tag -- node tag
    ]++
    concatMap set (zip [3..] xs)++
    [Clear (Memory "Hp" $ size-1),Val (Memory "Hp" $ size-1) size
    ,Clear (Memory "Hp" size) -- next frame
    ]++
    post (Memory "Hp" $ size-2)
    where
        size=5+length xs
        set (ix,v)=[Clear (Memory "Hp" ix),Val (Memory "Hp" ix) v]

-- | Compile 'GMCode's from given 'MPos' to 'Stmt's, followed by 'Origin' returning code.
contWith :: M.Map String Int -> MPos -> [GMCode] -> [Stmt] -> [Stmt]
contWith m Origin [] ss=ss
contWith m HeapA  [] ss=ss++[Inline "#heap1Hp" []]
contWith m StackA [] ss=ss++[Inline "#stack1S0" []]
contWith m StackT [] ss=ss++[Inline "#stack1S0" []]
contWith m prev xs@(x:_) ss=ss++transition prev (fPos x)++[Comment (show x)]++compileCode m xs

-- TODO: come up with good abstraction
transition :: MPos -> MPos -> [Stmt]
transition x y
    |x==y                   = []
    |x==Origin && y==StackT = [Inline "#stackTopS0" []]
    |x==Origin              = []
    |x==StackA && y==StackT = [Inline "#stackTopS0" []]
    |x==StackA && y==Origin = [Inline "#stack1S0" []]
    |x==StackA && y==HeapA  = [Inline "#stack1S0" []]
    |x==StackT && y==StackA = []
    |x==StackT && y==Origin = [Inline "#stack1S0" []]
    |x==StackT && y==HeapA  = [Inline "#stack1S0" []]
    |x==HeapA  && y==StackT = [Inline "#heap1Hp" [],Inline "#stackTopS0" []]
    |x==HeapA               = [Inline "#heap1Hp" []]

-- | Compile a single 'GMCode' to a procedure. StackA|HeapA -> StackA|HeapA
compileCode :: M.Map String Int -> [GMCode] -> [Stmt]
compileCode m (PushByte x:is)= -- constTag x
    contWith m StackT is $ newFrame constTag [x] $ \pa->
    [SAM.Alloc "addr"
    ,Copy pa [Register "addr"]
    ,Inline "#heap1Hp" []
    ,Inline "#stackNewS0" []
    ,Move (Register "addr") [Memory "S0" 0]
    ,Delete "addr"
    ]
compileCode m (PushSC k:is)= -- scTag sc
    contWith m StackT is $ newFrame scTag [m M.! k] $ \pa->
    [SAM.Alloc "addr"
    ,Copy pa [Register "addr"]
    ,Inline "#heap1Hp" []
    ,Inline "#stackNewS0" []
    ,Move (Register "addr") [Memory "S0" 0]
    ,Delete "addr"
    ]
compileCode m (MkApp:is)= -- appTag ap0 ap1
    contWith m HeapA is $ newFrame appTag [0,0] $ \pa->
    [SAM.Alloc "addr"
    ,Copy pa [Register "addr"]
    ,Inline "#heap1Hp" []
    ,Inline "#stackNewS0" []
    ,SAM.Alloc "tr1"
    ,Move (Memory "S0" (-1)) [Register "tr1"]
    ,SAM.Alloc "tr2"
    ,Move (Memory "S0" (-2)) [Register "tr2"]
    ,Copy (Register "addr") [Memory "S0" (-2)]
    ,Locate (-2)
    ,Inline "#stack1S0" []
    ,Inline "#heapRefHp" ["addr"]
    ,Delete "addr"
    ,Move (Register "tr1") [Memory "Hp" 3]
    ,Delete "tr1"
    ,Move (Register "tr2") [Memory "Hp" 4]
    ,Delete "tr2"
    ]
compileCode m (Pack t 0:is)=
    contWith m StackT is $ newFrame structTag [t] $ \pa->
    [SAM.Alloc "addr"
    ,Copy pa [Register "addr"]
    ,Inline "#heap1Hp" []
    ,Inline "#stackNewS0" []
    ,Move (Register "addr") [Memory "S0" 0]
    ,Delete "addr"
    ]
compileCode m (Pack t n:is)= -- stTag t x1...xn
    contWith m HeapA is $ newFrame structTag (t:replicate n 0) $ \pa->
    [SAM.Alloc "addr"
    ,Copy pa [Register "addr"]
    ,Inline "#heap1Hp" []
    ,Inline "#stackNewS0" []
    ]++
    concatMap (\n->let r="tr"++show n in [SAM.Alloc r,Move (Memory "S0" $ negate n) [Register r]]) [1..n]++
    [Copy (Register "addr") [Memory "S0" $ negate n]
    ,Locate $ negate n
    ,Inline "#stack1S0" []
    ,Inline "#heapRefHp" ["addr"]
    ,Delete "addr"
    ]++
    concatMap (\n->let r="tr"++show n in [Move (Register r) [Memory "Hp" $ n+3],Delete r]) [1..n]
compileCode m (UnPack 0:is)=contWith m StackT is $
    [Inline "#stackNewS0" []
    ,Clear (Memory "S0" (-1))
    ,Locate (-2)
    ]
compileCode m (UnPack n:is)=contWith m StackA is $ -- the last item becomes top
    [Inline "#stackNewS0" []
    ,SAM.Alloc "saddr"
    ,Move (Memory "S0" (-1)) [Register "saddr"]
    ,Locate (-2)
    ,Inline "#stack1S0" []
    ,Inline "#heapRefHp" ["saddr"]
    ,Delete "saddr"
    ]++
    map (SAM.Alloc . ("tr"++) . show) [1..n]++
    map (\x->Copy (Memory "Hp" $ 3+x) [Register $ "tr"++show x]) [1..n]++
    [Inline "#heap1Hp" []
    ,Inline "#stackNewS0" []
    ]++
    map (\x->Move (Register $ "tr"++show x) [Memory "S0" $ x-1]) (reverse [1..n])++
    map (Delete . ("tr"++) . show) [1..n]
compileCode m (Swap:is)=contWith m StackT is $
    [SAM.Alloc "temp"
    ,Move (Memory "S0" 0) [Register "temp"]
    ,Move (Memory "S0" (-1)) [Memory "S0" 0]
    ,Move (Register "temp") [Memory "S0" (-1)]
    ,Delete "temp"
    ]
compileCode m (Push n:is)=contWith m StackT is $
    [Inline "#stackNewS0" []
    ,Copy (Memory "S0" $ negate $ n+1) [Memory "S0" 0]
    ]
compileCode m (Slide n:is)=if n<=0 then error "Slide 0" else contWith m StackT is $
    [Clear (Memory "S0" $ negate n)
    ,Move (Memory "S0" 0) [Memory "S0" $ negate n]
    ]++
    map (Clear . Memory "S0" . negate) [1..n-1]++
    [Locate $ negate n]
compileCode m (PushArg n:is)=contWith m StackT is $
    [SAM.Alloc "aaddr"
    ,Copy (Memory "S0" $ negate n) [Register "aaddr"]
    ,Inline "#stack1S0" []
    ,Inline "#heapRefHp" ["aaddr"]
    ,Delete "aaddr"
    ,SAM.Alloc "arg"
    ,Copy (Memory "Hp" 4) [Register "arg"]
    ,Inline "#heap1Hp" []
    ,Inline "#stackNewS0" []
    ,Move (Register "arg") [Memory "S0" 0]
    ,Delete "arg"
    ]
compileCode m (Case cs:is)=contWith m Origin is $
    [SAM.Alloc "saddr"
    ,Copy (Memory "S0" 0) [Register "saddr"]
    ,Inline "#stack1S0" []
    ,Inline "#heapRefHp" ["saddr"]
    ,Delete "saddr"
    ,SAM.Alloc "tag"
    ,Copy (Memory "Hp" 3) [Register "tag"]
    ,Dispatch "tag" $ map (second $ flip (contWith m HeapA) []) cs
    ,Delete "tag"
    ]
compileCode m (Update n:is)=contWith m HeapA is $
    [SAM.Alloc "to"
    ,Move (Memory "S0" 0) [Register "to"]
    ,Locate (-1)
    ,SAM.Alloc "from"
    ,Copy (Memory "S0" $ 1-n) [Register "from"]
    ,Inline "#stack1S0" []
    -- rewrite stack
    ,While (Memory "S0" 0)
        [Inline "#rewriteS0" ["from","to"]
        ,Locate 1
        ]
    ,Locate (-1)
    ,Inline "#stack1S0" []
    -- rewrite heap
    ,While (Memory "Hp" 0)
        [SAM.Alloc "ntag"
        ,Copy (Memory "Hp" 2) [Register "ntag"]
        ,Dispatch "ntag"
            [(appTag,
                [Locate 3
                ,Inline "#rewriteHp" ["from","to"]
                ,Locate 1
                ,Inline "#rewriteHp" ["from","to"]
                ,Locate 3
                ])
            ,(scTag,
                [Locate 6])
            ,(constTag,
                [Locate 6])
            ,(structTag,
                [SAM.Alloc "size"
                ,Copy (Memory "Hp" 0) [Register "size"]
                ,Val (Register "size") (-6)
                ,Locate 4
                ,While (Register "size")
                    [Inline "#rewriteHp" ["from","to"]
                    ,Locate 1
                    ,Val (Register "size") (-1)
                    ]
                ,Delete "size"
                ,Locate 2
                ])
            ]
        ,Delete "ntag"
        ]
    ,Delete "from"
    ,Delete "to"
    ]
compileCode m (Pop n:is)=contWith m StackT is $
    concat $ replicate n [Clear (Memory "S0" 0),Locate (-1)]
compileCode m (GMachine.Alloc n:is)=compileCode m $ replicate n (PushByte 0)++is

compileCode m (UError s:_)=Clear ptr:concatMap (\d->[Val ptr d,Output ptr]) ds
    where
        ds=head ns:zipWith (-) (tail ns) ns
        ns=map ord s
        ptr=Memory "S0" 0
compileCode m (Arith op:is)=contWith m StackT is $
    [SAM.Alloc "x"
    ,SAM.Alloc "y"
    ,Move (Memory "S0" 0) [Register "x"]
    ,Move (Memory "S0" (-1)) [Register "y"]
    ,Locate (-2)
    ,Inline "#stack1S0" []
    ,Inline "#heapRefHp" ["x"]
    ,Copy (Memory "Hp" 3) [Register "x"]
    ,Inline "#heap1Hp" []
    ,Inline "#heapRefHp" ["y"]
    ,Delete "y"
    ,SAM.Alloc "temp"
    ,Copy (Memory "Hp" 3) [Register "temp"]
    ]++
    f (Register "temp") (Register "x") op++
    [Delete "temp"
    ,SAM.Alloc "addr"
    ,Inline "#heapNewHp" ["addr"]
    ,Clear (Memory "Hp" 0) ,Val (Memory "Hp" 0) 6
    ,Clear (Memory "Hp" 1) ,Val (Memory "Hp" 1) 0
    ,Clear (Memory "Hp" 2) ,Val (Memory "Hp" 2) $ tag op
    ,Clear (Memory "Hp" 3) ,Move (Register "x") [Memory "Hp" 3] ,Delete "x"
    ,Clear (Memory "Hp" 4) ,Copy (Register "addr") [Memory "Hp" 4]
    ,Clear (Memory "Hp" 5) ,Val (Memory "Hp" 5) 6
    ,Clear (Memory "Hp" 6)
    ,Inline "#heap1Hp" []
    ,Inline "#stackNewS0" []
    ,Move (Register "addr") [Memory "S0" 0]
    ,Delete "addr"
    ]
    where
        tag CCmp=structTag
        tag _=constTag
        f from to AAdd=[While from [Val from (-1),Val to 1]]
        f from to ASub=[While from [Val from (-1),Val to (-1)]]
        f from to CCmp=
            [SAM.Alloc "t"
            ,Val (Register "t") 1
            ,While (Register "t")
                [SAM.Alloc "s"
                ,Copy from [Register "s"]
                ,Val (Register "t") 1
                ,While (Register "s")
                    [Clear (Register "s")
                    ,Val (Register "t") (-1)
                    ]
                ,Copy to [Register "s"]
                ,While (Register "s")
                    [Clear (Register "s")
                    ,Val (Register "t") (-1)
                    ]
                ,Val (Register "s") 1
                ,While (Register "t")
                    [Clear (Register "t")
                    ,Val (Register "s") (-1)
                    ]
                ,Move (Register "s") [Register "t"]
                ,Delete "s"
                ,Val from (-1)
                ,Val to (-1)
                ]
            ,Val from 1
            ,Val to 1
            ,While from [Clear from,Val (Register "t") 1]
            ,While to [Clear to,Val (Register "t") 2]
            ,Move (Register "t") [to] -- 0:EQ 1:from>to 2:to<from
            ,Delete "t"
            ]
          






-- | G-machine intstruction
--
-- Note1: 'MkApp' 'Pack' ordering: first pushed -> last packed
--
-- Note2: 'PushArg' counts from top=0
data GMCode
    =Slide Int -- ^ pop 1st...nth items
    |Update Int -- ^ replace all reference to the nth address to 0th address.
    |Pop Int -- ^ remove n items
    |Push Int
    |PushSC String
    |Alloc Int
    |Swap -- ^ used for implementing 'elimReduce'
    |Reduce RHint -- ^ reduce stack top to WHNF
    -- function
    |MkApp -- ^ function must be pushed after arguments. then use this.
    |PushArg Int
    -- data structure
    |Pack Int Int
    |Case [(Int,[GMCode])]
    |UnPack Int
    -- arithmetic
    |PushByte Int
    |Arith ArithOp
    -- error
    |UError String -- ^ output the given string with undefined consequence
    deriving(Show)

data ArithOp
    =AAdd
    |ASub
    |CCmp
    deriving(Show)

data RHint
    =RByte
    |RE
    |RAny
    deriving(Show)

pprint :: M.Map String [GMCode] -> String
pprint=compileSB . Group . intersperse EmptyLine . map (uncurry pprintGMF) . M.assocs

pprintGMF :: String -> [GMCode] -> SBlock
pprintGMF name cs=Group
    [Line $ U.Pack [Prim name,Prim ":"]
    ,Indent $ Group $ map pprintGMC cs
    ]

pprintGMC :: GMCode -> SBlock
pprintGMC (Case cs)=Group
    [Line $ Prim "Case"
    ,Indent $ Group $ map (f . first show) $ sortBy (comparing fst) cs
    ]
    where f (label,xs)=Group [Line $ Span [Prim label,Prim "->"],Indent $ Group $ map pprintGMC xs]
pprintGMC c=Line $ Prim $ show c


-- | G-machine state for use in 'interpretGM'
type GMS=State GMInternal
type GMST m a=StateT GMInternal m a

data GMInternal=GMInternal{stack::Stack,heap::Heap} deriving(Show)
data GMNode
    =App Address Address
    |Const Int
    |Struct Int [Address]
    |Combinator String
    deriving(Show)

type Stack=[Address]
type Heap=M.Map Address GMNode

newtype Address=Address Int deriving(Show,Eq,Ord)





interpret :: M.Map String [GMCode] -> IO ()
interpret fs=evalStateT (evalGM False fs []) (makeEmptySt "main")

interpretR :: M.Map String [GMCode] -> IO ()
interpretR fs=evalStateT (evalGM True fs []) (makeEmptySt "main")

makeEmptySt :: String -> GMInternal
makeEmptySt entry=runIdentity $ execStateT (alloc (Combinator entry) >>= push) $ GMInternal [] M.empty


-- | Interpret a single combinator and returns new combinator to be executed.
evalGM :: Bool -> M.Map String [GMCode] -> [GMCode] -> GMST IO ()
evalGM fl fs []=do
    st<-get
    liftIO $ putStrLn $ "GMi: aux:\n"++showState st
    
    node<-refStack 0 >>= refHeap
    
    case node of
        App a0 a1 -> push a0 >> evalGM fl fs []
        Combinator x -> evalGM fl fs (fs M.! x)
        _ -> do x<-isRootNode
                if x
                    then case node of
                        Struct 0 [f] -> do
                            pop
                            x<-liftIO (liftM ord getChar)
                            alloc (Const x) >>= push >> push f >> evalGM fl fs [MkApp]
                        Struct 1 [x,k] -> do
                            pop
                            refHeap x >>= (liftIO . putChar . unConst)
                            push k
                            evalGM fl fs []
                        Struct 2 [] -> pop >> return ()
                    else when fl $ do{[e,c]<-popn 2; Combinator x<-refHeap c; push e; evalGM fl fs (fs M.! x)}
    where unConst (Const x)=chr x

evalGM fl fs (Reduce _:xs)=evalGM fl fs [] >> evalGM fl fs xs
evalGM fl fs (Push n:xs)=
    refStack n >>= push >> evalGM fl fs xs
evalGM fl fs (PushArg n:xs)=do
    App _ arg<-refStack n >>= refHeap
    push arg
    evalGM fl fs xs
evalGM fl fs (MkApp:xs)=do
    [s0,s1]<-popn 2
    alloc (App s0 s1) >>= push
    evalGM fl fs xs
evalGM fl fs (Pack t n:xs)=do
    ss<-popn n
    alloc (Struct t ss) >>= push
    evalGM fl fs xs
evalGM fl fs (PushSC n:xs)=do
    alloc (Combinator n) >>= push
    evalGM fl fs xs
evalGM fl fs (Slide n:xs)=do
    x<-pop
    popn n
    push x
    evalGM fl fs xs
evalGM fl fs (PushByte x:xs)=alloc (Const x) >>= push >> evalGM fl fs xs
evalGM fl fs (Case cs:xs)=do
    Struct t _<-refStack 0 >>= refHeap
    maybe (error $ "GMi: Case:"++show t) (evalGM fl fs . (++xs)) $ lookup t cs
evalGM fl fs (UnPack n:xs)=do
    Struct _ cs<-pop >>= refHeap
    when (length cs/=n) (error $ "GMi: UnPack arity error")
    mapM_ push cs
    evalGM fl fs xs
evalGM fl fs (Swap:xs)=popn 2 >>= mapM_ push >> evalGM fl fs xs
evalGM fl fs (Pop n:xs)=popn n >> evalGM fl fs xs
evalGM fl fs (Update n:xs)=do
    t<-pop
    f<-refStack $ n-1
    modify $ \(GMInternal st hp)->GMInternal (map (fS f t) st) (M.map (fH f t) hp)
    evalGM fl fs xs
    where
        fS f t x|x==f      = t
                |otherwise = x
        fH f t (App x y)=App (fS f t x) (fS f t y)
        fH f t (Struct tag xs)=Struct tag $ map (fS f t) xs
        fH _ _ x=x
evalGM fl fs (GMachine.Alloc n:xs)=evalGM fl fs $ replicate n (PushByte 0)++xs
evalGM fl fs (Arith op:xs)=do
    Const x<-pop >>= refHeap
    Const y<-pop >>= refHeap
    case op of
        AAdd -> alloc (Const $ (x+y) `mod` 256) >>= push
        ASub -> alloc (Const $ (x-y) `mod` 256) >>= push
        CCmp -> alloc (Struct (if x==y then 0 else if x<y then 1 else 2) []) >>= push
    evalGM fl fs xs
evalGM _ _ x=error $ "evalGM: unsupported: "++show x




showState :: GMInternal -> String
showState g=unlines $
    unwords (map show st):map (\(k,v)->show k++":"++show v) (M.assocs hp)
    where GMInternal st hp=GMachine.gc g


-- | do not modify pointers
gc :: GMInternal -> GMInternal
gc (GMInternal st hp)=GMInternal st hp'
    where
        hp'=M.filterWithKey (\k _ ->S.member k ns) $ hp
        ns=S.unions $ map (collect hp) st


collect heap addr=S.insert addr $
    case heap M.! addr of
        App a0 a1 -> S.union (collect heap a0) (collect heap a1)
        Struct _ as -> S.unions $ map (collect heap) as
        _ -> S.empty


refHeap :: Monad m => Address -> GMST m GMNode
refHeap addr=liftM ((M.!addr) . heap) get

refStack :: Monad m => Int -> GMST m Address
refStack n=liftM ((!!n) . stack) get

isRootNode :: Monad m => GMST m Bool
isRootNode=do
    n<-liftM (length . stack) get
    return $ n==1


push :: Monad m => Address -> GMST m ()
push addr=do
    GMInternal st h<-get
    put $ GMInternal (addr:st) h

alloc :: Monad m => GMNode -> GMST m Address
alloc n=do
    GMInternal st h<-get
    let addr=if M.null h then Address 0 else let Address base=fst $ M.findMax h in Address (base+1)
    put $ GMInternal st $ M.insert addr n h
    return addr

pop :: Monad m => GMST m Address
pop=do
    GMInternal (s:ss) h<-get
    put $ GMInternal ss h
    return s

popn :: Monad m => Int -> GMST m [Address]
popn=flip replicateM pop





