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
    |otherwise            = return $ SAM (ss++hs) (lib++prc++loop)
    where
        t=M.fromList $ ("main",2):zip (filter (/="main") $ M.keys m) [3..]
        
        -- code generation
        lib=[stack1,heap1,heapNew,heapNew_,heapRef,stackNew,stackTop]
        prc=map (uncurry $ compileProc t) $ M.assocs m
        loop=[rootProc,setupMemory,mainLoop,eval,evalApp,evalSC,evalStr,evalE,exec $ M.assocs t]
        
        -- layout configuration
        codeSpace=ceiling $ log (fromIntegral $ M.size m+2)/log 256
        heapSpace=1
        ss=map (("S"++) . show) [0..heapSpace-1]
        hs=["H0"]

simplify :: M.Map String [GMCode] -> Process (M.Map String [GMCode])
simplify=return . elimReduce

-- inlining condition:
-- 
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
    |Origin
    deriving(Show,Eq)

fPos :: GMCode -> MPos
fPos (PushByte _)=HeapA
fPos (PushSC _)=HeapA
fPos MkApp=HeapA
fPos (Pack _ _)=HeapA
fPos Swap=StackA
fPos (Push _)=StackA
fPos (Slide _)=StackA
fPos (PushArg _)=StackA
fPos (Case _)=StackA
fPos (UnPack _)=StackA



-- requirement: HF*
newFrame :: Int -> [Int] -> (Pointer -> [Stmt]) -> [Stmt]
newFrame tag xs post=
    [Comment $ unwords ["nf",show tag,show xs]
    ,SAM.Alloc "addr"
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

-- | Compile 'GMCode's from given 'MPos' to 'Stmt's, followed by 'Origin' returning code.
contWith :: M.Map String Int -> MPos -> [GMCode] -> [Stmt] -> [Stmt]
contWith m Origin [] ss=ss
contWith m HeapA  [] ss=ss++[Inline "#heap1" []]
contWith m StackA [] ss=ss++[Inline "#stack1" []]
contWith m prev xs@(x:_) ss=ss++transition prev (fPos x)++[Comment (show x)]++compileCode m xs

transition :: MPos -> MPos -> [Stmt]
transition x y
    |x==Origin || x==y = []
    |x==HeapA          = [Inline "#heap1" []]
    |x==StackA         = [Inline "#stack1" []]

-- | Compile a single 'GMCode' to a procedure. StackA|HeapA -> StackA|HeapA
compileCode :: M.Map String Int -> [GMCode] -> [Stmt]
compileCode m (PushByte x:is)= -- constTag x
    contWith m StackA is $ newFrame constTag [x] $ \pa->
    [SAM.Alloc "addr"
    ,Copy pa [Register "addr"]
    ,Inline "#heap1" []
    ,Inline "#stackNew" []
    ,Move (Register "addr") [Memory "S0" 0]
    ,Delete "addr"
    ]
compileCode m (PushSC k:is)= -- scTag sc
    contWith m StackA is $ newFrame scTag [m M.! k] $ \pa->
    [SAM.Alloc "addr"
    ,Copy pa [Register "addr"]
    ,Inline "#heap1" []
    ,Inline "#stackNew" []
    ,Move (Register "addr") [Memory "S0" 0]
    ,Delete "addr"
    ]
compileCode m (MkApp:is)= -- appTag ap0 ap1
    contWith m HeapA is $ newFrame appTag [0,0] $ \pa->
    [SAM.Alloc "addr"
    ,Copy pa [Register "addr"]
    ,Inline "#heap1" []
    ,Inline "#stackNew" []
    ,SAM.Alloc "tr1"
    ,Move (Memory "S0" (-1)) [Register "tr1"]
    ,SAM.Alloc "tr2"
    ,Move (Memory "S0" (-2)) [Register "tr2"]
    ,Copy (Register "addr") [Memory "S0" (-2)]
    ,Locate (-2)
    ,Inline "#stack1" []
    ,Inline "#heapRef" ["addr"]
    ,Delete "addr"
    ,Move (Register "tr1") [Memory "H0" 2]
    ,Delete "tr1"
    ,Move (Register "tr2") [Memory "H0" 3]
    ,Delete "tr2"
    ]
compileCode m (Pack t 0:is)=
    contWith m StackA is $ newFrame structTag [t] $ \pa->
    [SAM.Alloc "addr"
    ,Copy pa [Register "addr"]
    ,Inline "#heap1" []
    ,Inline "#stackNew" []
    ,Move (Register "addr") [Memory "S0" 0]
    ,Delete "addr"
    ]
compileCode m (Pack t n:is)= -- stTag t x1...xn
    contWith m HeapA is $ newFrame structTag (t:replicate n 0) $ \pa->
    [SAM.Alloc "addr"
    ,Copy pa [Register "addr"]
    ,Inline "#heap1" []
    ,Inline "#stackNew" []
    ]++
    concatMap (\n->let r="tr"++show n in [SAM.Alloc r,Move (Memory "S0" $ negate n) [Register r]]) [1..n]++
    [Copy (Register "addr") [Memory "S0" $ negate n]
    ,Locate $ negate n
    ,Inline "#stack1" []
    ,Inline "#heapRef" ["addr"]
    ,Delete "addr"
    ]++
    concatMap (\n->let r="tr"++show n in [Move (Register r) [Memory "H0" $ n+2],Delete r]) [1..n]
compileCode m (UnPack 0:is)=contWith m StackA is $
    [Inline "#stackNew" []
    ,Clear (Memory "S0" (-1))
    ,Locate (-2)
    ]
compileCode m (UnPack n:is)=contWith m StackA is $ -- the last item becomes top
    [Inline "#stackNew" []
    ,SAM.Alloc "saddr"
    ,Move (Memory "S0" (-1)) [Register "saddr"]
    ,Locate (-2)
    ,Inline "#stack1" []
    ,Inline "#heapRef" ["saddr"]
    ,Delete "saddr"
    ]++
    map (SAM.Alloc . ("tr"++) . show) [1..n]++
    map (\x->Copy (Memory "H0" $ 2+x) [Register $ "tr"++show x]) [1..n]++
    [Inline "#heap1" []
    ,Inline "#stackNew" []
    ]++
    map (\x->Move (Register $ "tr"++show x) [Memory "S0" $ x-1]) (reverse [1..n])++
    map (Delete . ("tr"++) . show) [1..n]
compileCode m (Swap:is)=contWith m StackA is $
    [Inline "#stackTop" []
    ,SAM.Alloc "temp"
    ,Move (Memory "S0" 0) [Register "temp"]
    ,Move (Memory "S0" (-1)) [Memory "S0" 0]
    ,Move (Register "temp") [Memory "S0" (-1)]
    ,Delete "temp"
    ]
compileCode m (Push n:is)=contWith m StackA is $
    [Inline "#stackNew" []
    ,Copy (Memory "S0" $ negate $ n+1) [Memory "S0" 0]
    ]
compileCode m (Slide 0:is)=contWith m StackA is []
compileCode m (Slide n:is)=contWith m StackA is $
    [Inline "#stackTop" []
    ,Clear (Memory "S0" $ negate n)
    ,Move (Memory "S0" 0) [Memory "S0" $ negate n]
    ]++
    map (Clear . Memory "S0" . negate) [1..n-1]++
    [Locate $ negate n]
compileCode m (PushArg n:is)=contWith m StackA is $
    [Inline "#stackTop" []
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
    ]
compileCode m (Case cs:is)=contWith m Origin is $
    [Inline "#stackTop" []
    ,SAM.Alloc "saddr"
    ,Copy (Memory "S0" 0) [Register "saddr"]
    ,Inline "#stack1" []
    ,Inline "#heapRef" ["saddr"]
    ,Delete "saddr"
    ,SAM.Alloc "tag"
    ,Copy (Memory "H0" 2) [Register "tag"]
    ,Dispatch "tag" $ map (second $ flip (contWith m HeapA) []) cs
    ,Delete "tag"
    ]
compileCode m (UError s:_)=
    [Clear ptr
    ,Val ptr 117
    ,Output ptr -- u
    ,Val ptr (-7)
    ,Output ptr -- n
    ,Val ptr (-10)
    ,Output ptr -- d
    ,Val ptr 1
    ,Output ptr -- e
    ,Val ptr 1
    ,Output ptr -- f
    ,Val ptr 3
    ,Output ptr -- i
    ,Val ptr 5
    ,Output ptr -- n
    ,Val ptr (-9)
    ,Output ptr -- e
    ,Val ptr (-1)
    ,Output ptr -- d
    ]
    where ptr=Memory "S0" 0


    
-- | Applicable for Pack, App
st2heap ix=
    [Inline "#heap1" []
    ,Inline "#stackTop" []
    ,SAM.Alloc "temp"
    ,Move (Memory "S0" 0) [Register "temp"]
    ,Locate (-1)
    ,Inline "#stack1" []
    ,Inline "#heapNew_" []
    ,Move (Register "temp") [Memory "H0" $ negate $ 2+ix]
    ,Delete "temp"
    ]

-- | Use this right after 'st2heap' to push newly created pointer
st2heapFin=
    [Inline "#heap1" []
    ,Inline "#stackNew" []
    ,Move (Register "addr") [Memory "S0" 0]
    ,Delete "addr"
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
--
-- this function calls 'evalApp', 'evalSC', 'evalStr' and evalConst after aligning with heap frame.
eval :: SProc
eval=SProc "%eval" ["sc"]
    [Inline "#stack1" []
    ,Inline "#stackTop" []
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
        ,(structTag,[Inline "%evalStr" ["sc"]])
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


evalStr=SProc "%evalStr" ["sc"]
    [Inline "#heap1" []
    ,Inline "#stackTop" []
    ,SAM.Alloc "root"
    ,Val (Register "root") 1
    ,While (Memory "S0" (-1)) -- non-root frame -> get sc
        [Val (Register "sc") (-1) -- sc:=0
        ,Val (Register "root") (-1)
        ,SAM.Alloc "addr"
        ,Move (Memory "S0" (-1)) [Register "addr"]
        ,Move (Memory "S0" 0) [Memory "S0" (-1)] -- move exp to top
        ,Locate (-1)
        ,Inline "#stack1" []
        ,Inline "#heapRef" ["addr"]
        ,Delete "addr"
        ,Copy (Memory "H0" 2) [Register "sc"]
        ,Inline "#heap1" []
        ]
    ,While (Register "root")
        [Val (Register "root") (-1)
        ,Inline "#stackTop" []
        ,SAM.Alloc "addr"
        ,Copy (Memory "S0" 0) [Register "addr"]
        ,Inline "#stack1" []
        ,Inline "#heapRef" ["addr"]
        ,Delete "addr"
        ,Inline "%evalE" ["sc"]
        ]
    ,Delete "root"
    ]

-- sc must be 1 on entry
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
            ,Inline "#stackTop" []
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
            ,Inline "#stackTop" []
            ,Clear (Memory "S0" 0)
            ,Move (Register "kaddr") [Memory "S0" 0]
            ,Delete "kaddr"
            ,Inline "#stack1" []
            ])
        ,(2, -- halt
            [Val (Register "sc") (-1) -- sc:=0
            ,Inline "#heap1" []
            ,Inline "#stackTop" []
            ,Clear (Memory "S0" 0)
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

-- | Move to stack new.
stackNew :: SProc
stackNew=SProc "#stackNew" []
    [While (Memory "S0" 0) [Locate 1]]

-- | Move to stack top.
stackTop :: SProc
stackTop=SProc "#stackTop" []
    [While (Memory "S0" 0) [Locate 1]
    ,Locate (-1)
    ]





-- | G-machine intstruction
--
-- Note1: 'MkApp' 'Pack' ordering: first pushed -> last packed
--
-- Note2: 'PushArg' counts from top=0
data GMCode
    =Slide Int -- ^ pop 1st...nth items
    |Update Int -- ^ \[n\]:=Ind &\[0\] and pop 1
    |Pop Int -- ^ remove n items
    |MkApp -- ^ function must be pushed after arguments. then use this.
    |Push Int
    |PushArg Int
    |PushSC String
    |PushByte Int
    |Pack Int Int
    |Case [(Int,[GMCode])]
    |UnPack Int
--    |Alloc Int
    |Reduce RHint -- ^ reduce stack top to WHNF
    |Swap -- ^ used for implementing 'elimReduce'
    |UError String -- ^ output the given string with undefined consequence
    deriving(Show)

data RHint
    =RByte
    |RE
    |RAny
    deriving(Show)

pprint :: M.Map String [GMCode] -> String
pprint=compileSB . U.Pack . map (uncurry pprintGMF) . M.assocs

pprintGMF :: String -> [GMCode] -> StrBlock
pprintGMF name cs=Line $ U.Pack [Line $ U.Pack [Prim name,Prim ":"],pprintGMCs cs]

pprintGMCs :: [GMCode] -> StrBlock
pprintGMCs=Indent . U.Pack . map pprintGMC

pprintGMC :: GMCode -> StrBlock
pprintGMC (Case cs)=U.Pack [Line $ Prim "Case",Indent $ U.Pack $ map f as]
    where
        as=map (first show) (sortBy (comparing fst) cs)
        f (label,x)=U.Pack [Line $ Prim $ label++"->",pprintGMCs x]
pprintGMC c=Line $ Prim $ show c


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
evalGM _ _ x=error $ "evalGM: unsupported: "++show x




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





