module SAM where
import Control.Monad
import Data.Array.IO
import Data.Char
import Data.Word

import Util
import Brainfuck


-- | Sequential Access Machine
data SAM=SAM [String] 
    deriving(Show)

data SAMProc=SAMProc String 


compile :: SAM -> Process BFM
compile x=return undefined

