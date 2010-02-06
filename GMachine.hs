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

import Util
import SAM


data GFCompileFlag=GFCompileFlag
    {addrSpace :: Int -- ^ bytes
    }


compile :: M.Map String [GMCode] -> Process SAM
compile m
    |codeSpace>1 = error "GM->SAM: 255+ super combinators are not supported"
    |heapSpace>1 = error "GM->SAM: 2+ byte addresses are not supported"
    |otherwise   = return $ SAM (ss++hs) [stack0]
    where
        codeSpace=ceiling $ log (fromIntegral $ M.size m+1)/log 256
        heapSpace=1
        ss=map (("S"++) . show) [0..heapSpace-1]
        hs=["H0"]
        


compileCode :: M.Map String Int -> GMCode -> SProc
compileCode m (PushSC k)=SProc ("PushSC"++show k) "S0" [] []
    where n=m M.! k
compileCode _ (Pack t n)=undefined
compileCode _ (Slide n)=undefined
compileCode _ (Push n)=undefined


stack0 :: SProc
stack0=SProc ("#stack0") "S0" []
    [While Memory
        [While Memory [Ptr (-1)]
        ,Bank "S0" "S1"
        ,While Memory [Ptr (-1)]
        ,Bank "S1" "S0"]
    ]





data GMCode
    =Slide Int -- ^ pop 1st...nth items
    |Alloc Int
    |Update Int -- ^ [n]:=Ind &[0] and pop 1
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
    deriving(Show)


pprintGM :: M.Map String [GMCode] -> String
pprintGM=compileSB 0 . intersperse SNewline . map (uncurry pprintGMF) . M.assocs

pprintGMF :: String -> [GMCode] -> StrBlock
pprintGMF name cs=SBlock
    [SPrim name,SPrim ":",SIndent,SNewline
    ,SBlock $ map (\x->SBlock [SPrim $ show x,SNewline]) cs]


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
        Combinator x -> return (Just x)
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




