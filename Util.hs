{-# LANGUAGE FlexibleInstances #-}
-- | Modular error reporting and common functions
--
-- note for future me: Arrow vs. Monad
--    Suppose each process can return either error or result.
--   Parallel execution of such processes can be written as:
--    (a -> m b) -> [a] -> m [b]  : Monadic form
--    w a b -> w [a] [b] : Arrow form
-- 
-- How to decide on one?
--    If you can write [m b] -> m [b] , then use Monad.
--   Otherwise use Arrow.
module Util(module Util,throwError) where
import Control.Arrow
import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Identity
import qualified Data.IntMap as IM
import Data.List
import Data.Word



-- | Process that may fail with ['CompileError']
-- ErrorT Identity is used for future use. (cf. ErrorT Writer)
type Process a=ErrorT [CompileError] Identity a

runProcess :: Process a -> Either [CompileError] a
runProcess=runIdentity . runErrorT

runProcessWithIO :: (a->IO ()) -> Process a -> IO ()
runProcessWithIO f=either (putStr . unlines . map show) f . runProcess




-- | A detailed compile error
-- 
-- * 'CompileError' is used in early stages where filename and line number is known
--
-- * 'CompileErrorN' is used in later stages where only non-numerical position is available
data CompileError
    =CompileError String String String -- ^ e.g. CompileError "Haskell->Core" "Main.hs:12" "parse error"
    |CompileErrorN String String [String] -- ^ e.g. CompileErrorN "SAM->SAM" "unknown register x" ["while","proc foo"]

instance Show CompileError where
    show (CompileError m p d)=m++":"++p++":\n"++d
    show (CompileErrorN m d ps)=m++":\n"++d++"\n"++concatMap (\x->"in "++x++"\n") ps

instance Error [CompileError] where
    noMsg=[]


-- | Nested structure multiple reporter monad
type NMR p e a=State ([p],[([p],e)]) a

report :: e -> NMR p e ()
report e=do
    (pos,es)<-get
    put (pos,(pos,e):es)

within :: p -> NMR p e a -> NMR p e a
within x f=do
    modify (first (x:))
    r<-f
    modify (first tail)
    return r

runNMR :: NMR p e a -> (a,[([p],e)])
runNMR=second snd . flip runState ([],[])





-- | Nested string with indent for general pretty printing
data StrBlock
    =Prim String
    |Pack [StrBlock]
    |Span [StrBlock]
    |Line StrBlock
    |Indent StrBlock

-- | Render 'StrBlock'
compileSB :: StrBlock -> String
compileSB=caux 0

caux :: Int -> StrBlock -> String
caux n (Prim x)=x
caux n (Pack ss)=concatMap (caux n) ss
caux n (Span ss)=concatMap (caux n) $ intersperse (Prim " ") ss
caux n (Line b)=replicate (4*n) ' '++caux n b++"\n"
caux n (Indent b)=caux (n+1) b





-- | Moderately fast memory suitable for use in interpreters.
data FlatMemory=FlatMemory (IM.IntMap Word8)

minit :: FlatMemory
minit=FlatMemory $ IM.empty

mread :: FlatMemory -> Int -> Word8
mread (FlatMemory m) i=maybe 0 id $ IM.lookup i m

mwrite :: FlatMemory -> Int -> Word8 -> FlatMemory
mwrite (FlatMemory m) i v=FlatMemory $ IM.insert i v m

mmodify :: FlatMemory -> Int -> (Word8 -> Word8) -> FlatMemory
mmodify fm i f=mwrite fm i (f $ mread fm i)




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

mapAt :: Int -> (a->a) -> [a] -> [a]
mapAt ix0 f=zipWith g [0..]
    where g ix x=if ix==ix0 then f x else x

fst3 (x,_,_)=x
snd3 (_,y,_)=y
thr3 (_,_,z)=z

