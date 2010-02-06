module SAM where
import Control.Monad
import Data.Array.IO
import Data.Char
import Data.Word

import Util
import Brainfuck


-- | Sequential Access Machine
data SAM=SAM [Region] [SProc]
    deriving(Show)

newtype Region=Region String deriving(Show,Eq)


data SProc=SProc String Region [Variable] Stmt deriving(Show)

data Stmt
    =Block [Stmt]
    |While Variable Stmt
    |Alloc Pointer
    |Delete Pointer
    |Inline String [String]
    |Dispatch Pointer [(Int,Stmt)]
    |Halt
    |Clear Pointer
    |Ptr Pointer Int
    |Val Pointer Int
    |Move Pointer [Pointer]
    deriving(Show)

data Pointer=Pointer deriving(Show)
data Variable=Variable deriving(Show)



compile :: SAM -> Process BFM
compile x=return undefined

