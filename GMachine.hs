-- | GMachine
-- reference: Implementing Functional Languages: a tutorial
--
-- GC is executed every 256 allocation.
module GMachine where
import Control.Monad
import Control.Monad.State
import Control.Monad.Identity
import Data.Char
import Data.List
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S

import Util as U hiding(Pack)
import qualified Util as U
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
-- * k B: payload
--
-- * n B: id of this frame
-- 
-- * 1 B: size of this frame 
--
-- Fields other than payload is always non-zero.
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
    |otherwise            = return $ SAM (ss++hs) (lib++cmd++prc++loop)
    where
        t=M.fromList $ ("main",2):zip (filter (/="main") $ M.keys m) [3..]
        
        -- code generation
        lib=[stack1,heap1,heapNew,heapNew_,heapRef,stackNew]
        cmd=map (compileCode t) $ nub $ concat $ M.elems m
        prc=map (uncurry compileCodeBlock) $ M.assocs m
        loop=[rootProc,setupMemory,mainLoop,eval,evalApp,evalSC,evalE,exec $ M.assocs t]
        
        -- layout configuration
        codeSpace=ceiling $ log (fromIntegral $ M.size m+1)/log 256
        heapSpace=1
        ss=map (("S"++) . show) [0..heapSpace-1]
        hs=["H0"]


-- | Compile a sequence of 'GMCode's to a procedure. 1->1
compileCodeBlock :: String -> [GMCode] -> SProc
compileCodeBlock name cs=SProc ("!"++name) [] $ map (flip Inline [] . compileName) cs


compileName :: GMCode -> String
compileName MkApp="%MkApp"
compileName (PushSC k)="%PushSC_"++k
compileName (Pack t n)="%Pack_"++show t++"_"++show n
compileName (Slide n)="%Slide_"++show n
compileName (PushArg n)="%PushArg_"++show n
compileName (PushByte x)="%PushByte_"++show x



-- requirement: HF*
newFrame :: Int -> [Int] -> (Pointer -> [Stmt]) -> [Stmt]
newFrame tag xs post=
    [SAM.Alloc "addr"
    ,Inline "#heapNew" ["addr"]
    ,Clear (Memory "H0" $ size-2)
    ,Move (Register "addr") [Memory "H0" $ size-2]
    ,Delete "addr"
    ,Val (Memory "H0" 0) size
    ,Clear (Memory "H0" 1),Val (Memory "H0" 1) tag
    ]++
    concatMap set (zip [2..] xs)++
    [Clear (Memory "H0" $ size-1),Val (Memory "H0" $ size-1) size
    ,Clear (Memory "H0" size) -- next frame
    ]++
    post (Memory "H0" $ size-2)
    where
        size=4+length xs
        set (ix,v)=[Clear (Memory "H0" ix),Val (Memory "H0" ix) v]


-- | Compile a single 'GMCode' to a procedure. 1->1
compileCode :: M.Map String Int -> GMCode -> SProc
compileCode m c=SProc (compileName c) [] $ case c of
    PushByte x -> -- constTag x
        newFrame constTag [x] $ \pa->
        [SAM.Alloc "addr"
        ,Copy pa [Register "addr"]
        ,Inline "#heap1" []
        ,Inline "#stackNew" []
        ,Move (Register "addr") [Memory "S0" 0]
        ,Delete "addr"
        ,Inline "#stack1" []
        ]
    PushSC k -> -- scTag sc
        newFrame scTag [m M.! k] $ \pa->
        [SAM.Alloc "addr"
        ,Copy pa [Register "addr"]
        ,Inline "#heap1" []
        ,Inline "#stackNew" []
        ,Move (Register "addr") [Memory "S0" 0]
        ,Delete "addr"
        ,Inline "#stack1" []
        ]
    MkApp -> -- appTag ap0 ap1
        newFrame appTag [0,0] $ \pa->
        [SAM.Alloc "addr"
        ,Copy pa [Register "addr"]
        ]++
        concatMap st2heap [2,1]++
        heap2st
    Pack t n -> -- stTag t x1...xn
        newFrame structTag (t:replicate n 0) $ \pa->
        [SAM.Alloc "addr"
        ,Copy pa [Register "addr"]
        ]++
        concatMap st2heap (reverse $ [1..n])++ -- pack struct members from back to front
        heap2st
    Slide n ->
        [Inline "#stackNew" []
        ,Locate (-1)
        ,Clear (Memory "S0" $ negate n)
        ,Move (Memory "S0" 0) [Memory "S0" $ negate n]
        ]++
        map (Clear . Memory "S0" . negate) [1..n-1]++
        [Locate $ negate n
        ,Inline "#stack1" []
        ]
    PushArg n ->
        [Inline "#stackNew" []
        ,Locate (-1)
        ,SAM.Alloc "aaddr"
        ,Copy (Memory "S0" $ negate n) [Register "aaddr"]
        ,Inline "#stack1" []
        ,Inline "#heapRef" ["aaddr"]
        ,Delete "aaddr"
        ,SAM.Alloc "arg"
        ,Copy (Memory "H0" 3) [Register "arg"]
        ,Inline "#heap1" []
        ,Inline "#stackNew" []
        ,Move (Register "arg") [Memory "S0" 0]
        ,Delete "arg"
        ,Inline "#stack1" []
        ]
    
    where
        st2heap ix= -- applicable for Pack, App
            [Inline "#heap1" []
            ,Inline "#stackNew" []
            ,Locate (-1)
            ,SAM.Alloc "temp"
            ,Move (Memory "S0" 0) [Register "temp"]
            ,Locate (-1)
            ,Inline "#stack1" []
            ,Inline "#heapNew_" []
            ,Move (Register "temp") [Memory "H0" $ negate $ 2+ix]
            ,Delete "temp"
            ]
        heap2st= -- use this right after st2heap to push newly created pointer
            [Inline "#heap1" []
            ,Inline "#stackNew" []
            ,Move (Register "addr") [Memory "S0" 0]
            ,Delete "addr"
            ,Inline "#stack1" []
            ]

    
appTag=0
scTag=1
constTag=2
structTag=3
refTag=4


rootProc :: SProc
rootProc=SProc "^" []
    [Inline "%setupMemory" []
    ,Inline "%mainLoop" []
    ]


setupMemory :: SProc
setupMemory=SProc "%setupMemory" []
    [Locate 1
    ,Val (Memory "S0" 0) 1 -- frame addr
    ,Val (Memory "H0" 0) 5 -- frame size
    ,Val (Memory "H0" 1) scTag
    ,Val (Memory "H0" 2) sc
    ,Val (Memory "H0" 3) 1 -- frame addr
    ,Val (Memory "H0" 4) 5 -- frame size
    ]
    where sc=2 -- main

mainLoop :: SProc
mainLoop=SProc "%mainLoop" []
    [SAM.Alloc "sc" -- 0:halt 1:cont-eval *:exec
    ,Val (Register "sc") 1
    ,While (Register "sc")
        [Inline "%eval" ["sc"]
        ,Inline "%exec" ["sc"]
        ]
    ,Delete "sc"
    ]

-- | Eval. Must be on address 1. /sc/ must be 1 on entry.
--
-- * halt: sc:=0
--
-- * eval: sc:=1
--
-- * exec: sc:=2-255
eval :: SProc
eval=SProc "%eval" ["sc"]
    [Inline "#stack1" []
    ,Inline "#stackNew" []
    ,Locate (-1) -- stack top
    ,SAM.Alloc "addr"
    ,Copy (Memory "S0" 0) [Register "addr"]
    ,Inline "#stack1" []
    ,Inline "#heapRef" ["addr"]
    ,Delete "addr"
    ,SAM.Alloc "tag"
    ,Copy (Memory "H0" 1) [Register "tag"]
    ,Dispatch "tag"
        [(appTag,[Inline "%evalApp" []])
        ,(scTag,[Inline "%evalSC" ["sc"]])
        ,(constTag,[])
        ,(structTag,[Inline "%evalE" ["sc"]])
        ]
    ,Delete "tag"
    ]

evalApp=SProc "%evalApp" []
    [SAM.Alloc "addr"
    ,Copy (Memory "H0" 2) [Register "addr"]
    ,Inline "#heap1" []
    ,Inline "#stackNew" []
    ,Move (Register "addr") [Memory "S0" 0]
    ,Delete "addr"
    ,Inline "#stack1" []
    ]

evalSC=SProc "%evalSC" ["sc"]
    [Val (Register "sc") (-1)
    ,Copy (Memory "H0" 2) [Register "sc"]
    ,Inline "#heap1" []
    ]

evalE=SProc "%evalE" ["sc"]
    [SAM.Alloc "stag"
    ,Copy (Memory "H0" 2) [Register "stag"]
    ,Dispatch "stag"
        [(0, -- input f
            [SAM.Alloc "faddr"
            ,Copy (Memory "H0" 3) [Register "faddr"]
            -- construct app frame: [6,appTag,f,aaddr+1,aaddr,6]
            ,SAM.Alloc "aaddr"
            ,Inline "#heapNew" ["aaddr"]
            ,Val (Memory "H0" 0) 6
            ,Clear (Memory "H0" 1),Val (Memory "H0" 1) appTag
            ,Clear (Memory "H0" 2),Move (Register "faddr") [Memory "H0" 2]
            ,Delete "faddr"
            ,Clear (Memory "H0" 3),Clear (Memory "H0" 4),Clear (Memory "H0" 5)
            ,Copy (Register "aaddr") [Memory "H0" 3,Memory "H0" 4]
            ,Val (Memory "H0" 3) 1
            ,Val (Memory "H0" 5) 6
            ,Clear (Memory "H0" 6) -- mark new frame
            -- construct const frame: [5,constTag,input,aaddr+1,5]
            ,Locate 6
            ,Clear (Memory "H0" 1)
            ,Clear (Memory "H0" 3)
            ,Clear (Memory "H0" 4)
            ,Val (Memory "H0" 0) 5
            ,Val (Memory "H0" 1) constTag
            ,Copy (Register "aaddr") [Memory "H0" 3],Val (Memory "H0" 3) 1
            ,Val (Memory "H0" 4) 5
            ,Input (Memory "H0" 2)
            ,Clear (Memory "H0" 5) -- mark new frame
            -- pop and push aaddr
            ,Inline "#heap1" []
            ,Inline "#stackNew" []
            ,Locate (-1)
            ,Clear (Memory "S0" 0)
            ,Move (Register "aaddr") [Memory "S0" 0]
            ,Delete "aaddr"
            ,Inline "#stack1" []
            ])
        ,(1, -- output x k [7,structTag,1,X,K,addr,7]
            [SAM.Alloc "xaddr"
            ,SAM.Alloc "kaddr"
            ,Copy (Memory "H0" 3) [Register "xaddr"]
            ,Copy (Memory "H0" 4) [Register "kaddr"]
            -- refer and output x
            ,Inline "#heap1" []
            ,Inline "#heapRef" ["xaddr"]
            ,Delete "xaddr"
            ,Output (Memory "H0" 2)
            -- replace stack top
            ,Inline "#heap1" []
            ,Inline "#stackNew" []
            ,Locate (-1)
            ,Clear (Memory "S0" 0)
            ,Move (Register "kaddr") [Memory "S0" 0]
            ,Delete "kaddr"
            ,Inline "#stack1" []
            ])
        ,(2, -- halt
            [Val (Register "sc") (-1) -- sc:=0
            ,Inline "#heap1" []
            ,Inline "#stackNew" []
            ,Clear (Memory "S0" (-1))
            ,Locate (-1)
            ])
        ]
    ,Delete "stag"
    ]

-- | Must be on address 1. /sc/ will be 1 or 0.
exec :: [(String,Int)] -> SProc
exec xs=SProc "%exec" ["sc"]
    [SAM.Alloc "cont"
    ,While (Register "sc")
        [Dispatch "sc" $ (1,[]):map f xs
        ,Val (Register "cont") 1
        ]
    ,While (Register "cont")
        [Val (Register "sc") 1
        ,Val (Register "cont") (-1)
        ]
    ,Delete "cont"
    ]
    where f (str,n)=(n,[Inline ("!"++str) []])



-- | Return to address 1. Must be aligned with a heap frame.
heap1 :: SProc
heap1=SProc "#heap1" []
    [While (Memory "H0" (-1))
        [SAM.Alloc "cnt"
        ,Copy (Memory "H0" (-1)) [Register "cnt"]
        ,While (Register "cnt")
            [Val (Register "cnt") (-1)
            ,Locate (-1)
            ]
        ,Delete "cnt"
        ]
    ]

-- | Move to where a new heap frame would be and write the address to addr. Must be aligned with frame.
-- The first size field is 0, but others are undefined.
heapNew :: SProc
heapNew=SProc "#heapNew" ["addr"]
    [While (Memory "H0" 0)
        [SAM.Alloc "cnt"
        ,Copy (Memory "H0" 0) [Register "cnt"]
        ,While (Register "cnt")
            [Val (Register "cnt") (-1)
            ,Locate 1]
        ,Delete "cnt"
        ]
    ,Copy (Memory "H0" (-2)) [Register "addr"]
    ,Val (Register "addr") 1
    ]

-- | Move to where a new heap frame would be. Must be aligned with frame.
-- The first size field is 0, but others are undefined.
heapNew_ :: SProc
heapNew_=SProc "#heapNew_" []
    [While (Memory "H0" 0)
        [SAM.Alloc "cnt"
        ,Copy (Memory "H0" 0) [Register "cnt"]
        ,While (Register "cnt")
            [Val (Register "cnt") (-1)
            ,Locate 1]
        ,Delete "cnt"
        ]
    ]

-- | Move to the frame pointed by addr. addr will be 0. Must be aligned.
heapRef :: SProc
heapRef=SProc "#heapRef" ["addr"]
    [Val (Register "addr") (-1)
    ,While (Register "addr")
        [Val (Register "addr") (-1)
        ,SAM.Alloc "cnt"
        ,Copy (Memory "H0" 0) [Register "cnt"]
        ,While (Register "cnt")
            [Val (Register "cnt") (-1)
            ,Locate 1
            ]
        ,Delete "cnt"
        ]
    ]

-- | Return to address 1. Must be on stack($S\/=0).
stack1 :: SProc
stack1=SProc "#stack1" []
    [While (Memory "S0" 0) [Locate (-1)],Locate 1]

-- | Move to stack top.
stackNew :: SProc
stackNew=SProc "#stackNew" []
    [While (Memory "S0" 0) [Locate 1]]







-- | G-machine intstruction
--
-- Note1: 'MkApp' 'Pack' ordering: first pushed -> last packed
--
-- Note2: 'PushArg' counts from top=0
data GMCode
    =Slide Int -- ^ pop 1st...nth items
    |Alloc Int
    |Update Int -- ^ \[n\]:=Ind &\[0\] and pop 1
    |Pop Int -- ^ remove n items
    |MkApp -- ^ function must be pushed after arguments. then use this.
    |Eval
    |PushArg Int
    |PushSC String
    |PushByte Int
    |Pack Int Int
    |Casejump [(Int,GMCode)]
    |Split Int
    deriving(Show,Eq,Ord)


pprintGM :: M.Map String [GMCode] -> String
pprintGM=compileSB . U.Pack . map (uncurry pprintGMF) . M.assocs

pprintGMF :: String -> [GMCode] -> StrBlock
pprintGMF name cs=Line $ U.Pack
    [Line $ U.Pack [Prim name,Prim ":"]
    ,Indent $ U.Pack $ map (Line . Prim . show) cs]


-- | G-machine state for use in 'interpretGM'
type GMS=State GMInternal
type GMST m a=StateT GMInternal m a

data GMInternal=GMInternal{stack::Stack,heap::Heap} deriving(Show)
data GMNode
    =App Address Address
    |Ref Address
    |Const Int
    |Struct Int [Address]
    |Combinator String
    deriving(Show)

type Stack=[Address]
type Heap=M.Map Address GMNode

newtype Address=Address Int deriving(Show,Eq,Ord)





interpretGM :: M.Map String [GMCode] -> IO ()
interpretGM fs=evalStateT (exec []) (makeEmptySt "main")
    where exec code=aux code >>= maybe (return ()) (exec . (fs M.!))

makeEmptySt :: String -> GMInternal
makeEmptySt entry=runIdentity $ execStateT (alloc (Combinator entry) >>= push) $ GMInternal [] M.empty


-- | Interpret a single combinator and returns new combinator to be executed.
aux :: [GMCode] -> GMST IO (Maybe String)
aux (c:cs)=evalGM c >> aux cs
aux []=do
    st<-get
    liftIO $ putStrLn $ "GMi: aux:\n"++showState st
    
    node<-refStack 0 >>= refHeap
    case node of
        App a0 a1 -> push a0 >> aux []
        Combinator x -> return (Just x) -- do not pop here, because the callee contains the code to remove it with arguments
        Struct 0 [f] -> do
            pop
            x<-liftIO (liftM ord getChar)
            evalGM (PushByte x) >> push f >> evalGM MkApp
            aux []
        Struct 1 [x,k] -> do
            pop
            refHeap x >>= (liftIO . putChar . unConst)
            push k
            aux []
        Struct 2 [] -> pop >> return Nothing
    where unConst (Const x)=chr x


showState :: GMInternal -> String
showState g=unlines $
    unwords (map show st):map (\(k,v)->show k++":"++show v) (M.assocs hp)
    where GMInternal st hp=gc g


-- | do not modify pointers
gc :: GMInternal -> GMInternal
gc (GMInternal st hp)=GMInternal st hp'
    where
        hp'=M.filterWithKey (\k _ ->S.member k ns) $ hp
        ns=S.unions $ map (collect hp) st


collect heap addr=S.insert addr $
    case heap M.! addr of
        App a0 a1 -> S.union (collect heap a0) (collect heap a1)
        Ref a -> collect heap a
        Struct _ as -> S.unions $ map (collect heap) as
        _ -> S.empty


refHeap0 :: Monad m => Address -> GMST m GMNode
refHeap0 addr=liftM ((M.!addr) . heap) get

refHeap :: Monad m => Address -> GMST m GMNode
refHeap addr=do
    n<-refHeap0 addr
    case n of
        Ref addr' -> refHeap addr'
        _ -> return n

refStack :: Monad m => Int -> GMST m Address
refStack n=liftM ((!!n) . stack) get

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



-- | /Pure/ evaluation
evalGM :: Monad m => GMCode -> GMST m ()
evalGM (PushArg n)=do
    App _ arg<-refStack n >>= refHeap
    push arg
evalGM MkApp=do
    [s0,s1]<-popn 2
    alloc (App s0 s1) >>= push
evalGM (Pack t n)=do
    ss<-popn n
    alloc (Struct t ss) >>= push
evalGM (PushSC n)=do
    alloc (Combinator n) >>= push
evalGM (Slide n)=do
    x<-pop
    popn n
    push x
evalGM (PushByte x)=alloc (Const x) >>= push
evalGM x=error $ "evalGM: unsupported: "++show x




