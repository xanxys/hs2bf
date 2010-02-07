{-# LANGUAGE FlexibleInstances #-}
-- | Modular error reporting and common functions
module Util where
import Control.Monad.Error
import Control.Monad.Identity
import qualified Data.IntMap as IM
import Data.Word



-- | Process that may fail with ['CompileError']
-- ErrorT Identity is used for future use. (cf. ErrorT Writer)
type Process a=ErrorT [CompileError] Identity a

runProcess :: Process a -> Either [CompileError] a
runProcess=runIdentity . runErrorT




-- | a compile error
-- 
-- * corresponding part of program (ex.: frontend, core)
--
-- * position (inline)
--
-- * error descriptipn(multiple line)
data CompileError=CompileError String String String

instance Show CompileError where
    show (CompileError m p d)=m++":"++p++"\n"++d

instance Error [CompileError] where
    noMsg=[]


-- note for future me: Arrow vs. Monad
--    Suppose each process can return either error or result.
--   Parallel execution of such processes can be written as:
--    (a -> m b) -> [a] -> m [b]  : Monadic form
--    w a b -> w [a] [b] : Arrow form
-- 
-- How to decide on one?
--    If you can write [m b] -> m [b] , then use Monad(Plus).
--   Otherwise use Arrow.


-- | a b c ... z aa ab ac ... az ba ...
-- avoid CAF.
stringSeq :: String -> [String]
stringSeq prefix=tail $ map ((prefix++) . reverse) $ iterate stringInc []

stringInc :: String -> String
stringInc []="a"
stringInc ('z':xs)='a':stringInc xs
stringInc (x:xs)=succ x:xs

-- | usage
--
-- > change1 "XYZ" "abc"
--
-- evaluates to
--
-- > ["Xbc","aYc","abZ"]
change1 :: [a] -> [a] -> [[a]]
change1 (x:xs) (y:ys)=(x:ys):map (y:) (change1 xs ys)
change1 _ _=[]


-- | Nested string with indent for general pretty printing
data StrBlock
    =SBlock [StrBlock]
    |SPrim String
    |SSpace
    |SNewline
    |SIndent


-- | Render ['StrBlock'] with an inital indentation
compileSB :: Int -> [StrBlock] -> String
compileSB _ []=""
compileSB n ((SBlock ss):xs)=compileSB n ss++compileSB n xs
compileSB n ((SPrim s):xs)=s++compileSB n xs
compileSB n (SSpace:xs)=" "++compileSB n xs
compileSB n (SNewline:xs)="\n"++replicate (n*4) ' '++compileSB n xs
compileSB n (SIndent:xs)=compileSB (n+1) xs



-- | Moderately fast memory suitable for use in interpreters.
data FlatMemory=FlatMemory (IM.IntMap Word8)

mread :: FlatMemory -> Int -> Word8
mread (FlatMemory m) i=maybe 0 id $ IM.lookup i m

mwrite :: FlatMemory -> Int -> Word8 -> FlatMemory
mwrite (FlatMemory m) i v=FlatMemory $ IM.insert i v m

mmodify :: FlatMemory -> Int -> (Word8 -> Word8) -> FlatMemory
mmodify fm i f=mwrite fm i (f $ mread fm i)



