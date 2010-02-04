module GMachine where
import Control.Monad
import Control.Monad.State
import Data.Char
import Data.Maybe
import qualified Data.Map as M

import Util
import Brainfuck

data GMCode
    =Slide Int
    |Alloc Int
    |Update Int
    |Pop Int
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

data GFCompileFlag=GFCompileFlag
    {addrSpace :: Int -- ^ bytes
    }



pprintGM :: M.Map String [GMCode] -> String
pprintGM=compileSB 0 . map (uncurry pprintGMF) . M.assocs

pprintGMF :: String -> [GMCode] -> StrBlock
pprintGMF name cs=SBlock
    [SPrim name,SPrim ":",SIndent,SNewline
    ,SBlock $ map (\x->SBlock [SPrim $ show x,SNewline]) cs
    ,SDedent,SNewline]



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


compile :: M.Map String [GMCode] -> Process BF0
compile m=return $ BF0 []


interpretGM :: M.Map String [GMCode] -> IO ()
interpretGM fs=evalStateT (exec "main") emptySt
    where exec name=aux (fs M.! name) >>= maybe (return ()) exec

emptySt :: GMInternal
emptySt=GMInternal [] M.empty


-- | Interpret a single combinator and returns new combinator to be executed.
aux :: [GMCode] -> GMST IO (Maybe String)
aux (c:cs)=trans (evalGM c) >> aux cs
aux []=do
    node<-trans $ refStack 0 >>= refHeap
    case node of
        App a0 a1 -> trans (push a0) >> aux []
        Combinator x -> trans pop >> return (Just x)
        Struct 0 [f] -> trans pop >> liftIO (liftM ord getChar) >>= \x->aux [MkByte x]
        Struct 1 [x,k] -> trans pop >> trans (refHeap x) >>= liftIO . putChar . f >> trans (push k) >> aux []
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


