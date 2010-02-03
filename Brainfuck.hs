-- | Brainfuck(BF2,BF1,BF0) optimizer
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

import Error


data BF0
    =BF0PInc
    |BF0PDec
    |BF0VInc
    |BF0VDec
    |BF0Begin
    |BF0End
    |BF0Input
    |BF0Output
    |BF0Loop [BF0] -- ^ a little bit high-level construct
    deriving(Show)

-- | Assume /standard/ environment. That is
--
-- * [0,+inf) address space
--
-- * Each cell consists of a byte which represents Z256.
--
-- * Moving into negative address immediately causes an error.
interpretBF0 :: [BF0] -> IO ()
interpretBF0 is=newArray (0,1000) 0 >>= evalBF0 (detectLoop is) 0

evalBF0 :: [BF0] -> Int -> IOUArray Int Word8 -> IO ()
evalBF0 [] ptr arr=return ()
evalBF0 (BF0PInc:is) ptr arr=do
    pmax<-liftM snd $ getBounds arr
    if ptr>=pmax
        then getElems arr >>= newListArray (0,pmax*2+1) . (++replicate (pmax+1) 0) >>= evalBF0 is (ptr+1)
        else evalBF0 is (ptr+1) arr
evalBF0 (BF0PDec:is) ptr arr=evalBF0 is (ptr-1) arr
evalBF0 (BF0VInc:is) ptr arr=readArray arr ptr >>= writeArray arr ptr . (+1) >> evalBF0 is ptr arr
evalBF0 (BF0VDec:is) ptr arr=readArray arr ptr >>= writeArray arr ptr . (+(-1)) >> evalBF0 is ptr arr
evalBF0 (BF0Input:is) ptr arr=getChar >>= writeArray arr ptr . fromIntegral . ord >> evalBF0 is ptr arr
evalBF0 (BF0Output:is) ptr arr=readArray arr ptr >>= putChar . chr . fromIntegral >> evalBF0 is ptr arr
evalBF0 is0@(BF0Loop ss:is) ptr arr=do
    flag<-readArray arr ptr
    if flag==0 then evalBF0 is ptr arr else evalBF0 ss ptr arr >> evalBF0 is0 ptr arr


detectLoop is=pprog is


-- PROG=EXPR*
-- EXPR=PRIM|BEGIN EXPR* END

pprog []=[]
pprog is=let (t,is')=takeOne is in t:pprog is'

takeOne (BF0Begin:is)=let (ts,is')=ploop is in (BF0Loop ts,is')
takeOne (BF0End:_)=error "missing Begin"
takeOne (i:is)=(i,is)

ploop []=error "missing End"
ploop (BF0End:is)=([],is)
ploop is=let (t,is')=takeOne is in let (ts,is'')=ploop is' in (t:ts,is'')





