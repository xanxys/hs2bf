-- | Super-cool-graph-representation
module SCGR where

import Util
import Brainfuck

type SCGR=BF

compile :: SCGR -> Process BF
compile=return

