-- | GMachine
-- reference: Implementing Functional Languages: a tutorial
--
-- GC is executed every 256 allocation.
module GMachine where
import Control.Monad
import Control.Monad.State
import Data.Char
import Data.List
import Data.Maybe
import qualified Data.Map as M

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
    |codeSpace>1 = error "GM->SAM: 255+ super combinator is not supported"
    |heapSpace>1 = error "GM->SAM: 2+ byte addresses are not supported"
    |otherwise   = return $ SAM (ss++hs) (lib++cmd++prc++loop)
    where
        t=M.fromList $ ("main",1):zip (filter (/="main") $ M.keys m) [2..]
        
        -- code generation
        lib=[stack1,heap1,heapNew,heapNew_,heapRef,stackNew]
        cmd=map (compileCode t) $ nub $ concat $ M.elems m
        prc=map (uncurry compileCodeBlock) $ M.assocs m
        loop=[rootProc,setupMemory,mainLoop,eval,exec $ M.assocs t]
        
        -- layout configuration
        codeSpace=ceiling $ log (fromIntegral $ M.size m+1)/log 256
        heapSpace=1
        ss=map (("S"++) . show) [0..heapSpace-1]
        hs=["H0"]


compileCodeBlock :: String -> [GMCode] -> SProc
compileCodeBlock name cs=SProc ("!"++name) [] $ map (flip Inline [] . compileName) cs


compileName :: GMCode -> String
compileName (PushSC k)="%PushSC_"++k
compileName (Pack t n)="%Pack_"++show t++"_"++show n
compileName (Slide n) ="%Slide_"++show n
compileName (Push n)  ="%Push_"++show n

-- | Compile a single 'GMCode' to a procedure. 1->1
compileCode :: M.Map String Int -> GMCode -> SProc
compileCode m c=SProc (compileName c) [] $ cap $ case c of
    PushSC k -> -- [5,scTag,sc,id,5]
        [SAM.Alloc "temp"
        ,Inline "#heapNew" ["temp"]
        ,Clear (Memory "H0" 3)
        ,SAM.Alloc "addr"
        ,Move (Register "temp") [Memory "H0" 3,Register "addr"]
        ,Delete "temp"
        ,Clear (Memory "H0" 1)
        ,Clear (Memory "H0" 2)
        ,Clear (Memory "H0" 4)
        ,Val (Memory "H0" 0) 5
        ,Val (Memory "H0" 1) scTag
        ,Val (Memory "H0" 2) $ m M.! k
        ,Val (Memory "H0" 4) 5
        ,Clear (Memory "H0" 5) -- next frame
        ,Inline "#heap1" []
        ,Inline "#stackNew" []
        ,Move (Register "addr") [Memory "S0" 0]
        ,Delete "addr"
        ]
    Pack t n -> -- [5+n,stTag,t...id,5+n]
        [SAM.Alloc "addr"
        ,Inline "#heapNew" ["addr"]
        ,Clear (Memory "H0" $ 3+n),Move (Register "addr") [Memory "H0" $ 3+n]
        ,Delete "addr"
        ,Val (Memory "H0" 0) $ 5+n -- size
        ,Clear (Memory "H0" 1),Val (Memory "H0" 1) structTag -- frame tag
        ,Clear (Memory "H0" 2),Val (Memory "H0" 2) t -- struct tag
        ,Clear (Memory "H0" $ 4+n) -- size
        ,Clear (Memory "H0" $ 5+n) -- new frame
        ,SAM.Alloc "temp"
        ]
        ++concatMap st2heap (reverse [1..n]) -- pack struct members from back to front
        ++[SAM.Delete "temp"]
        where st2heap ix=[Inline "#heap1" []
                         ,Inline "#stackNew" []
                         ,Locate (-1)
                         ,Move (Memory "S0" 0) [Register "temp"]
                         ,Inline "#stack1" []
                         ,Inline "#heapNew_" []
                         ,Move (Register "temp") [Memory "H0" $ negate $ 1+ix]
                         ]
    Slide n ->
        [Inline "#stackNew" []
        ,Locate (-1)
        ,Move (Memory "S0" 0) [Memory "S0" $ negate n]
        ]
        ++map (Clear . Memory "S0" . negate) [1..n-1]
    Push n ->
        [Inline "#stackNew" []
        ,SAM.Alloc "temp"
        ,Move (Memory "S0" $ negate $ n+1) [Memory "S0" 0,Register "temp"]
        ,Move (Register "temp") [Memory "S0" $ negate $ n+1]
        ,Delete "temp"
        ]
    where cap ss=ss++[Inline "#heap1" []]
    
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
    where sc=1

mainLoop :: SProc
mainLoop=SProc "%mainLoop" []
    [SAM.Alloc "sc"
    ,Val (Register "sc") 1 -- any non-zero number will do
    ,While (Register "sc")
        [Inline "%eval" ["sc"]
        ,Inline "%exec" ["sc"]
        ]
    ,Delete "sc"
    ]

-- | Eval. Must be on address 1.
eval :: SProc
eval=SProc "%eval" ["sc"]
    [Inline "#stack1" []
    ,Inline "#stackNew" []
    ,Locate (-1) -- stack top
    ,SAM.Alloc "addr"
    ,SAM.Alloc "ta"
    ,Move (Memory "S0" 0) [Register "ta"]
    ,Move (Register "ta") [Register "addr",Memory "S0" 0]
    ,Delete "ta"
    ,Inline "#stack1" []
    ,Inline "#heapRef" ["addr"]
    ,Delete "addr"
    ,SAM.Alloc "tag"
    ,SAM.Alloc "temp"
    ,Move (Memory "H0" 1) [Register "temp"]
    ,Move (Register "temp") [Memory "H0" 1,Register "tag"]
    ,Dispatch "tag"
        [(scTag,
            [Move (Memory "H0" 2) [Register "temp"]
            ,Move (Register "temp") [Memory "H0" 2,Register "sc"]
            ])
        ,(structTag,
            [Move (Memory "H0" 2) [Register "temp"]
            ,SAM.Alloc "stag"
            ,Move (Register "temp") [Memory "H0" 2,Register "stag"]
            ,Dispatch "stag"
                [(0, -- input f
                    [])
                ,(1, -- output x k
                    [])
                ,(2, -- halt
                    [Clear (Register "sc")
                    ,Inline "#heap1" []
                    ,Locate 1
                    ,Inline "#stackNew" []
                    ,Clear (Memory "S0" (-1))
                    ])
                ]
            ,Delete "stag"
            ])
        ]
    ,Delete "tag"
    ,Delete "temp"
    ]

-- | Must be on address 1.
exec :: [(String,Int)] -> SProc
exec xs=SProc "%exec" ["sc"]
    [SAM.Alloc "temp"
    ,SAM.Alloc "temp2"
    ,Move (Register "sc") [Register "temp",Register "temp2"]
    ,Move (Register "temp") [Register "sc"]
    ,Delete "temp"
    ,Dispatch "temp2" $ map f xs
    ,Delete "temp2"
    ]
    where f (str,n)=(n,[Inline ("!"++str) []])



-- | Return to address 1. Must be aligned with a heap frame.
heap1 :: SProc
heap1=SProc "#heap1" []
    [While (Memory "H0" (-1))
        [SAM.Alloc "temp"
        ,SAM.Alloc "cnt"
        ,Move (Memory "H0" (-1)) [Register "temp"]
        ,Move (Register "temp") [Memory "H0" (-1),Register "cnt"]
        ,Delete "temp"
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
    [SAM.Alloc "temp"
    ,While (Memory "H0" 0)
        [Move (Memory "H0" 0) [Register "addr"]
        ,Move (Register "addr") [Memory "H0" 0,Register "temp"]
        ,While (Register "temp")
            [Val (Register "temp") (-1)
            ,Locate 1]
        ]
    ,Move (Memory "H0" (-2)) [Register "temp",Register "addr"]
    ,Move (Register "temp") [Memory "H0" (-2)]
    ,Delete "temp"
    ,Val (Register "addr") 1
    ]

-- | Move to where a new heap frame would be. Must be aligned with frame.
-- The first size field is 0, but others are undefined.
heapNew_ :: SProc
heapNew_=SProc "#heapNew_" []
    [SAM.Alloc "temp"
    ,SAM.Alloc "cnt"
    ,While (Memory "H0" 0)
        [Move (Memory "H0" 0) [Register "temp"]
        ,Move (Register "temp") [Memory "H0" 0,Register "cnt"]
        ,While (Register "cnt")
            [Val (Register "cnt") (-1)
            ,Locate 1]
        ]
    ,Delete "temp"
    ,Delete "cnt"
    ]

-- | Move to the frame pointed by addr. addr will be 0. Must be aligned.
heapRef :: SProc
heapRef=SProc "#heapRef" ["addr"]
    [Val (Register "addr") (-1)
    ,While (Register "addr")
        [SAM.Alloc "temp"
        ,SAM.Alloc "cnt"
        ,Move (Memory "H0" 0) [Register "temp"]
        ,Move (Register "temp") [Memory "H0" 0,Register "cnt"]
        ,Delete "temp"
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








data GMCode
    =Slide Int -- ^ pop 1st...nth items
    |Alloc Int
    |Update Int -- ^ \[n\]:=Ind &\[0\] and pop 1
    |Pop Int -- ^ remove n items
    |MkApp
    |Eval
    |Push Int
    |PushSC String
    |PushByte Int
    |Pack Int Int
    |Casejump [(Int,GMCode)]
    |Split Int
    |MkByte Int
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
makeEmptySt entry=execState (alloc (Combinator entry) >>= push) $ GMInternal [] M.empty


-- | Interpret a single combinator and returns new combinator to be executed.
aux :: [GMCode] -> GMST IO (Maybe String)
aux (c:cs)=trans (evalGM c) >> aux cs
aux []=do
    node<-trans $ refStack 0 >>= refHeap
    case node of
        App a0 a1 -> trans (push a0) >> aux []
        Combinator x -> return (Just x) -- do not pop here, because the callee contains the code to remove it with arguments
        Struct 0 [f] -> trans pop >> liftIO (liftM ord getChar) >>= \x->aux [MkByte x]
        Struct 1 [x,k] -> trans pop >> trans (refHeap x) >>= liftIO . putChar . f >>
                          trans (push k) >> aux []
        Struct 2 [] -> trans pop >> return Nothing
    where f (Const x)=chr x


-- | Convert 'State' monad to a 'StateT' without chaning its function.
trans :: Monad m => State s a -> StateT s m a
trans (State f)=StateT (\s->return $ f s)


refHeap0 :: Address -> GMS GMNode
refHeap0 addr=liftM ((M.!addr) . heap) get

refHeap :: Address -> GMS GMNode
refHeap addr=do
    n<-refHeap0 addr
    case n of
        Ref addr' -> refHeap addr'
        _ -> return n

refStack :: Int -> GMS Address
refStack n=liftM ((!!n) . stack) get

push :: Address -> GMS ()
push addr=do
    GMInternal st h<-get
    put $ GMInternal (addr:st) h

alloc :: GMNode -> GMS Address
alloc n=do
    GMInternal st h<-get
    let addr=if M.null h then Address 0 else let Address base=fst $ M.findMax h in Address (base+1)
    put $ GMInternal st $ M.insert addr n h
    return addr

pop :: GMS Address
pop=do
    GMInternal (s:ss) h<-get
    put $ GMInternal ss h
    return s

popn :: Int -> GMS [Address]
popn=flip replicateM pop



-- | /Pure/ evaluation
evalGM :: GMCode -> GMS ()
evalGM (Push n)=refStack (n+1) >>= push
evalGM MkApp=do
    [s0,s1]<-popn 2 
    n<-alloc (App s0 s1)
    push n
evalGM (Pack t n)=do
    ss<-popn n
    alloc (Struct t ss) >>= push
evalGM (PushSC n)=do
    alloc (Combinator n) >>= push
evalGM (Slide n)=do
    x<-pop
    popn n
    push x




