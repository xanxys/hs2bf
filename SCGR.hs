-- | Super-cool-graph-representation
--
-- There are 3 goals in optimization:
--
-- * Code size
--
-- * Memory usage
--
-- * Speed
--
-- And there are practically 3 types of optimization:
--
-- * -code +speed : o
--
-- * +code -speed : o
--
-- * -code +mem -speed : x (this is what you do when hand-writing /hello world/ in BF)
module SCGR where

import Util
import Brainfuck

type SCGR=BF



compile :: SCGR -> Process BF
compile=return

