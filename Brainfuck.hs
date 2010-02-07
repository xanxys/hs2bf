-- | Brainfuck: backend of /super-cool-graph-machine/. No serious work is done here.
--
-- Cost model of BF.
--
-- * All instructions are executed in a common constant duration.
--
-- * Input command requires unknown latency in addition to it.
module Brainfuck where
import Control.Monad
import Data.Array.IO
import Data.Char
import Data.Word

import Util






-- | Original brainfuck.
data BF=BF [BFInst]

data BFInst
    =BFPInc
    |BFPDec
    |BFVInc
    |BFVDec
    |BFBegin
    |BFEnd
    |BFInput
    |BFOutput
    |BFLoop [BFInst] -- ^ a little bit high-level construct

instance Show BF where
    show (BF is)=concatMap show is

instance Show BFInst where
    show BFPInc=">"
    show BFPDec="<"
    show BFVInc="+"
    show BFVDec="-"
    show BFBegin="["
    show BFEnd="]"
    show BFInput=","
    show BFOutput="."
    show (BFLoop ss)="["++concatMap show ss++"]"


-- | Assume /standard/ environment. That is
--
-- * [0,+inf) address space
--
-- * Each cell consists of a byte which represents Z256.
--
-- * Moving into negative address immediately causes an error.
interpretBF :: BF -> IO ()
interpretBF (BF is)=newArray (0,1000) 0 >>= evalBF (detectLoop is) 0

evalBF :: [BFInst] -> Int -> IOUArray Int Word8 -> IO ()
evalBF [] ptr arr=return ()
evalBF (BFPInc:is) ptr arr=do
    pmax<-liftM snd $ getBounds arr
    if ptr>=pmax
        then getElems arr >>= newListArray (0,pmax*2+1) . (++replicate (pmax+1) 0) >>= evalBF is (ptr+1)
        else evalBF is (ptr+1) arr
evalBF (BFPDec:is) ptr arr=evalBF is (ptr-1) arr
evalBF (BFVInc:is) ptr arr=readArray arr ptr >>= writeArray arr ptr . (+1) >> evalBF is ptr arr
evalBF (BFVDec:is) ptr arr=readArray arr ptr >>= writeArray arr ptr . (+(-1)) >> evalBF is ptr arr
evalBF (BFInput:is) ptr arr=getChar >>= writeArray arr ptr . fromIntegral . ord >> evalBF is ptr arr
evalBF (BFOutput:is) ptr arr=readArray arr ptr >>= putChar . chr . fromIntegral >> evalBF is ptr arr
evalBF is0@(BFLoop ss:is) ptr arr=do
    flag<-readArray arr ptr
    if flag==0 then evalBF is ptr arr else evalBF ss ptr arr >> evalBF is0 ptr arr


detectLoop is=pprog is


-- PROG=EXPR*
-- EXPR=PRIM|BEGIN EXPR* END

pprog []=[]
pprog is=let (t,is')=takeOne is in t:pprog is'

takeOne (BFBegin:is)=let (ts,is')=ploop is in (BFLoop ts,is')
takeOne (BFEnd:_)=error "missing Begin"
takeOne (i:is)=(i,is)

ploop []=error "missing End"
ploop (BFEnd:is)=([],is)
ploop is=let (t,is')=takeOne is in let (ts,is'')=ploop is' in (t:ts,is'')





