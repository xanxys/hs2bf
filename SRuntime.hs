module SRuntime where
import SAM

appTag=0
scTag=1
constTag=2
structTag=3


genLibrary :: [Int] -> [SProc]
genLibrary ns=concat
    [genStackLib "S0" -- primary address stack
    ,genStackLib "Hp" -- frontier stack in GC
    ,genHeapLib "Hp" -- primiary heap
    ,genHeapLib "Hs" -- secondary heap for GC
    ,[gc,gcTransfer,gcMark ns,gcCopy,gcIndex,gcRewrite]
    ,[rootProc,setupMemory,mainLoop,eval,evalApp,evalSC,evalStr,evalE]
    ,[isEqual,rewrite "S0",rewrite "Hp"]
    ]

rootProc :: SProc
rootProc=SProc "^" []
    [Inline "%setupMemory" []
    ,Inline "%mainLoop" []
    ]


setupMemory :: SProc
setupMemory=SProc "%setupMemory" []
    [Locate 1
    ,Val (Memory "S0" 0) 1 -- frame addr
    ,Val (Memory "Hp" 0) 6 -- frame size
    ,Val (Memory "Hp" 1) 0 -- GC tag
    ,Val (Memory "Hp" 2) scTag
    ,Val (Memory "Hp" 3) sc
    ,Val (Memory "Hp" 4) 1 -- frame addr
    ,Val (Memory "Hp" 5) 6 -- frame size
    ]
    where sc=2 -- main

mainLoop :: SProc
mainLoop=SProc "%mainLoop" []
    [Alloc "sc" -- 0:halt 1:cont-eval *:exec
    ,Val (Register "sc") 1
    ,While (Register "sc")
        [Inline "%eval" ["sc"]
        ,Inline "%exec" ["sc"]
        ]
    ,Delete "sc"
    ]

-- | Eval. Must be on address 1. /sc/ must be 1 on entry.
--
-- * halt: sc:=0
--
-- * eval: sc:=1
--
-- * exec: sc:=2-255
--
-- this function calls 'evalApp', 'evalSC', 'evalStr' and evalConst after aligning with heap frame.
eval :: SProc
eval=SProc "%eval" ["sc"]
    [Inline "#stack1S0" []
    ,Inline "#stackTopS0" []
    ,Alloc "addr"
    ,Copy (Memory "S0" 0) [Register "addr"]
    ,Inline "#stack1S0" []
    ,Inline "#heapRefHp" ["addr"]
    ,Delete "addr"
    ,Alloc "tag"
    ,Copy (Memory "Hp" 2) [Register "tag"]
    ,Dispatch "tag"
        [(appTag,[Inline "%evalApp" []])
        ,(scTag,[Inline "%evalSC" ["sc"]])
        ,(constTag,[])
        ,(structTag,[Inline "%evalStr" ["sc"]])
        ]
    ,Delete "tag"
    ]

evalApp=SProc "%evalApp" []
    [Alloc "addr"
    ,Copy (Memory "Hp" 3) [Register "addr"]
    ,Inline "#heap1Hp" []
    ,Inline "#stackNewS0" []
    ,Move (Register "addr") [Memory "S0" 0]
    ,Delete "addr"
    ,Inline "#stack1S0" []
    ]

evalSC=SProc "%evalSC" ["sc"]
    [Val (Register "sc") (-1)
    ,Copy (Memory "Hp" 3) [Register "sc"]
    ,Inline "#heap1Hp" []
    ]


evalStr=SProc "%evalStr" ["sc"]
    [Inline "#heap1Hp" []
    ,Inline "#stackTopS0" []
    ,Alloc "root"
    ,Val (Register "root") 1
    ,While (Memory "S0" (-1)) -- non-root frame -> get sc
        [Val (Register "sc") (-1) -- sc:=0
        ,Val (Register "root") (-1)
        ,Alloc "addr"
        ,Move (Memory "S0" (-1)) [Register "addr"]
        ,Move (Memory "S0" 0) [Memory "S0" (-1)] -- move exp to top
        ,Locate (-1)
        ,Inline "#stack1S0" []
        ,Inline "#heapRefHp" ["addr"]
        ,Delete "addr"
        ,Copy (Memory "Hp" 3) [Register "sc"]
        ,Inline "#heap1Hp" []
        ]
    ,While (Register "root")
        [Val (Register "root") (-1)
        ,Inline "#stackTopS0" []
        ,Alloc "addr"
        ,Copy (Memory "S0" 0) [Register "addr"]
        ,Inline "#stack1S0" []
        ,Inline "#heapRefHp" ["addr"]
        ,Delete "addr"
        ,Inline "%evalE" ["sc"]
        ]
    ,Delete "root"
    ]

-- sc must be 1 on entry
evalE=SProc "%evalE" ["sc"]
    [Alloc "stag"
    ,Copy (Memory "Hp" 3) [Register "stag"]
    ,Dispatch "stag"
        [(0, -- input f
            [Alloc "faddr"
            ,Copy (Memory "Hp" 4) [Register "faddr"]
            -- construct app frame: [7,gcTag,appTag,f,aaddr+1,aaddr,7]
            ,Alloc "aaddr"
            ,Inline "#heapNewHp" ["aaddr"]
            ,Val (Memory "Hp" 0) 7
            ,Clear (Memory "Hp" 1),Val (Memory "Hp" 1) 0
            ,Clear (Memory "Hp" 2),Val (Memory "Hp" 2) appTag
            ,Clear (Memory "Hp" 3),Move (Register "faddr") [Memory "Hp" 3]
            ,Delete "faddr"
            ,Clear (Memory "Hp" 4),Clear (Memory "Hp" 5),Clear (Memory "Hp" 6)
            ,Copy (Register "aaddr") [Memory "Hp" 4,Memory "Hp" 5]
            ,Val (Memory "Hp" 4) 1
            ,Val (Memory "Hp" 6) 7
            ,Clear (Memory "Hp" 7) -- mark new frame
            -- construct const frame: [6,gcTag,constTag,input,aaddr+1,6]
            ,Locate 7
            ,Clear (Memory "Hp" 1)
            ,Clear (Memory "Hp" 2)
            ,Clear (Memory "Hp" 3)
            ,Clear (Memory "Hp" 4)
            ,Val (Memory "Hp" 0) 6
            ,Val (Memory "Hp" 1) constTag
            ,Copy (Register "aaddr") [Memory "Hp" 4],Val (Memory "Hp" 4) 1
            ,Val (Memory "Hp" 5) 6
            ,Input (Memory "Hp" 3)
            ,Clear (Memory "Hp" 6) -- mark new frame
            -- pop and push aaddr
            ,Inline "#heap1Hp" []
            ,Inline "#stackTopS0" []
            ,Clear (Memory "S0" 0)
            ,Move (Register "aaddr") [Memory "S0" 0]
            ,Delete "aaddr"
            ,Inline "#stack1S0" []
            ])
        ,(1, -- output x k [8,gcTag,structTag,1,X,K,addr,8]
            [Alloc "xaddr"
            ,Alloc "kaddr"
            ,Copy (Memory "Hp" 4) [Register "xaddr"]
            ,Copy (Memory "Hp" 5) [Register "kaddr"]
            -- refer and output x
            ,Inline "#heap1Hp" []
            ,Inline "#heapRefHp" ["xaddr"]
            ,Delete "xaddr"
            ,Output (Memory "Hp" 3)
            -- replace stack top
            ,Inline "#heap1Hp" []
            ,Inline "#stackTopS0" []
            ,Clear (Memory "S0" 0)
            ,Move (Register "kaddr") [Memory "S0" 0]
            ,Delete "kaddr"
            ,Inline "#stack1S0" []
            ])
        ,(2, -- halt
            [Val (Register "sc") (-1) -- sc:=0
            ,Inline "#heap1Hp" []
            ,Inline "#stackTopS0" []
            ,Clear (Memory "S0" 0)
            ])
        ]
    ,Delete "stag"
    ]

-- | Must be on address 1. /sc/ will be 1 or 0.
exec :: [(String,Int)] -> SProc
exec xs=SProc "%exec" ["sc"]
    [Alloc "cont"
    ,While (Register "sc")
        [Dispatch "sc" $ (1,[]):map f xs
        ,Val (Register "cont") 1
        ]
    ,While (Register "cont")
        [Val (Register "sc") 1
        ,Val (Register "cont") (-1)
        ]
    ,Delete "cont"
    ]
    where f (str,n)=(n,[Inline ("!"++str) []])



genHeapLib :: String -> [SProc]
genHeapLib r=map ($r) [heap1,heapNew,heapNew_,heapTop,heapRef]

-- | Return to address 1. Must be aligned with a heap frame.
heap1 :: String -> SProc
heap1 r=SProc ("#heap1"++r) []
    [While (Memory r (-1))
        [Alloc "cnt"
        ,Copy (Memory r (-1)) [Register "cnt"]
        ,While (Register "cnt")
            [Val (Register "cnt") (-1)
            ,Locate (-1)
            ]
        ,Delete "cnt"
        ]
    ]

-- | Move to where a new heap frame would be and write the address to addr. Must be aligned with frame.
-- The first size field is 0, but others are undefined.
heapNew :: String -> SProc
heapNew r=SProc ("#heapNew"++r) ["addr"]
    [While (Memory r 0)
        [Alloc "cnt"
        ,Copy (Memory r 0) [Register "cnt"]
        ,While (Register "cnt")
            [Val (Register "cnt") (-1)
            ,Locate 1]
        ,Delete "cnt"
        ]
    ,Copy (Memory r (-2)) [Register "addr"]
    ,Val (Register "addr") 1
    ]

-- | Move to where a new heap frame would be. Must be aligned with frame.
-- The first size field is 0, but others are undefined.
heapNew_ :: String -> SProc
heapNew_ r=SProc ("#heapNew_"++r) []
    [While (Memory r 0)
        [Alloc "cnt"
        ,Copy (Memory r 0) [Register "cnt"]
        ,While (Register "cnt")
            [Val (Register "cnt") (-1)
            ,Locate 1]
        ,Delete "cnt"
        ]
    ]

-- | Move to where the heap top. Must be aligned with frame.
heapTop :: String -> SProc
heapTop r=SProc ("#heapTop"++r) []
    [While (Memory r 0)
        [Alloc "cnt"
        ,Copy (Memory r 0) [Register "cnt"]
        ,While (Register "cnt")
            [Val (Register "cnt") (-1)
            ,Locate 1]
        ,Delete "cnt"
        ]
    ,Alloc "cnt"
    ,Copy (Memory r (-1)) [Register "cnt"]
    ,While (Register "cnt")
        [Val (Register "cnt") (-1)
        ,Locate (-1)
        ]
    ,Delete "cnt"
    ]

-- | Move to the frame pointed by addr. addr will be 0. Must be aligned.
heapRef :: String -> SProc
heapRef r=SProc ("#heapRef"++r) ["addr"]
    [Val (Register "addr") (-1)
    ,While (Register "addr")
        [Val (Register "addr") (-1)
        ,Alloc "cnt"
        ,Copy (Memory r 0) [Register "cnt"]
        ,While (Register "cnt")
            [Val (Register "cnt") (-1)
            ,Locate 1
            ]
        ,Delete "cnt"
        ]
    ]

-- | Generate all stack utiltiy functions for given region.
genStackLib r=map ($r) [stack1,stackNew,stackTop]

-- | Return to address 1. Must be on stack($S\/=0).
stack1 :: String -> SProc
stack1 r=SProc ("#stack1"++r) []
    [While (Memory r 0) [Locate (-1)],Locate 1]

-- | Move to stack new.
stackNew :: String -> SProc
stackNew r=SProc ("#stackNew"++r) []
    [While (Memory r 0) [Locate 1]]

-- | Move to stack top.
stackTop :: String -> SProc
stackTop r=SProc ("#stackTop"++r) []
    [While (Memory r 0) [Locate 1]
    ,Locate (-1)
    ]


-- | Origin -> Origin: Run packing GC.
gc :: SProc
gc=SProc "#gc" []
    [Inline "#gcTransfer" []
    ,Inline "#gcMark" []
    ,Inline "#gcCopy" []
    ,Inline "#gcIndex" []
    ,Inline "#gcRewrite" []
    ]

-- | Copy everything as is from Hp to Hs.
gcTransfer :: SProc
gcTransfer=SProc "#gcTransfer" []
    [While (Memory "Hp" 0)
        [Alloc "cnt"
        ,Copy (Memory "Hp" 0) [Register "cnt"]
        ,While (Register "cnt")
            [Clear (Memory "Hs" 0)
            ,Move (Memory "Hp" 0) [Memory "Hs" 0]
            ,Val (Register "cnt") (-1)
            ,Locate 1
            ]
        ,Delete "cnt"
        ]
    ,Inline "#heap1s" []
    ]
        
-- | Mark nodes from S, using Hp as /frontier/ stack. Argument is cons arity.
gcMark :: [Int] -> SProc
gcMark ns=SProc "#gcMark" []
    [Comment "init frontiers"
    ,While (Memory "S0" 0)
        [Clear (Memory "Hp" 0)
        ,Copy (Memory "S0" 0) [Memory "Hp" 0]
        ,Locate 1
        ]
    ,Clear (Memory "Hp" 0)
    ,Locate (-1)
    ,Inline "#stack1S0" []
    ,Comment "top to bottom"
    ,Inline "#stackTopHp" []
    ,While (Memory "Hp" 0)
        [Alloc "addr"
        ,Move (Memory "Hp" 0) [Register "addr"]
        ,Locate (-1)
        ,Inline "#stack1Hp" []
        ,Inline "#heapRefHs" ["addr"]
        ,Delete "addr"
        ,Comment "flag:=1-gc; gc:=0"
        ,Alloc "flag"
        ,Val (Register "flag") 1
        ,While (Memory "Hs" 1)
            [Val (Memory "Hs" 1) (-1)
            ,Val (Register "flag") (-1)
            ]
        ,Val (Memory "Hs" 1) 1
        ,While (Register "flag")
            [Val (Register "flag") (-1)
            ,Alloc "ntag"
            ,Copy (Memory "Hs" 2) [Register "ntag"]
            ,Dispatch "ntag" $
                [(appTag,
                    [Alloc "t1"
                    ,Copy (Memory "Hs" 3) [Register "t1"]
                    ,Alloc "t2"
                    ,Copy (Memory "Hs" 4) [Register "t2"]
                    ,Inline "#heap1Hs" []
                    ,Inline "#stackNewHp" []
                    ,Move (Register "t1") [Memory "Hp" 0]
                    ,Delete "t1"
                    ,Move (Register "t2") [Memory "Hp" 1]
                    ,Delete "t2"
                    ,Clear (Memory "Hp" 2)
                    ,Locate 1
                    ])
                ,(scTag,
                    [Inline "#heap1Hs" []
                    ,While (Memory "Hp" 0) [Inline "#stackTopHp" []]
                    ])
                ,(constTag,
                    [Inline "#heap1Hs" []
                    ,While (Memory "Hp" 0) [Inline "#stackTopHp" []]
                    ])
                ]++
                if null ns then [] else
                [(structTag,
                    [Alloc "sz"
                    ,Copy (Memory "Hs" 0) [Register "sz"]
                    ,Dispatch "sz" $ map f ns
                    ,Delete "sz"
                    ])
                ]
            ,Delete "ntag"
            ]
        ,Delete "flag"
        ]
    ]
    where
        f n=(n+6,
            concatMap (\x->[Alloc $ "t"++show x,Copy (Memory "Hs" $ x+3) [Register $ "t"++show x]]) [1..n]++
            [Inline "#heap1Hs" []
            ,Inline "#stackNewHp" []
            ]++
            concatMap (\x->[Move (Register $ "t"++show x) [Memory "Hp" $ x-1],Delete $ "t"++show x]) [1..n]++
            [Clear (Memory "Hp" n),Locate $ n-1]
            )



-- | Copy marked frames from Hs to Hp.
gcCopy :: SProc
gcCopy=SProc "#gcCopy" []
    [While (Memory "Hs" 0)
        [Alloc "cnt"
        ,Move (Memory "Hs" 0) [Register "cnt"]
        ,Alloc "flag"
        ,Move (Memory "Hs" 1) [Register "flag"]
        ,Dispatch "flag"
            [(0,
                [While (Register "cnt")
                    [Val (Register "cnt") (-1)
                    ,Locate 1
                    ]
                ])
            ,(1,
                [While (Register "cnt")
                    [Val (Register "cnt") (-1)
                    ,Clear (Memory "Hp" 0)
                    ,Move (Memory "Hs" 0) [Memory "Hp" 0]
                    ,Locate 1
                    ]
                ])
            ]
        ,Delete "cnt"
        ,Delete "flag"
        ]
    ,Clear (Memory "Hp" 0)
    ,Inline "#heap1Hp" []
    ]

-- | Construct OldAddr->NewAddr table in Hs.
--
-- O(n^2)
gcIndex :: SProc
gcIndex=SProc "#gcIndex" []
    [Alloc "naddr"
    ,While (Memory "Hp" 0)
        [Alloc "cnt"
        ,Copy (Memory "Hp" 0) [Register "cnt"]
        ,While (Register "cnt")
            [Val (Register "cnt") (-1)
            ,Locate 1
            ]
        ,Delete "cnt"
        ,Val (Register "naddr") 1
        ]
    ,While (Register "naddr")
        [Alloc "ta"
        ,Copy (Register "naddr") [Register "ta"]
        ,Val (Register "ta") 1
        ,Inline "#heapRefHp" ["ta"]
        ,Delete "ta"
        ,Alloc "oaddr"
        ,Copy (Memory "Hp" (-2)) [Register "oaddr"]
        ,Inline "#heap1Hp" []
        ,Comment "Write index"
        ,Alloc "cnt"
        ,Copy (Register "oaddr") [Register "cnt"]
        ,While (Register "oaddr")
            [Val (Register "cnt") (-1)
            ,Locate 1
            ]
        ,Delete "cnt"
        ,Locate (-1)
        ,Clear (Memory "Hs" 0)
        ,Copy (Register "naddr") [Memory "Hs" 0]
        ,While (Register "oaddr")
            [Val (Register "oaddr") (-1)
            ,Locate (-1)
            ]
        ,Delete "oaddr"
        ,Locate 1
        ,Val (Register "naddr") (-1)
        ]        
    ,Delete "naddr"
    ,Comment "Rewrite id field"
    ]

-- | Rewrite stack and Hp addressed based on the table in Hs.
gcRewrite :: SProc
gcRewrite=SProc "#gcRewrite" []
    []

isEqual :: SProc
isEqual=SProc "#isEqual" ["x","y","f"]
    [While (Register "x")
        [Val (Register "x") (-1)
        ,Val (Register "y") (-1)
        ]
    ,Val (Register "f") 1
    ,While (Register "y")
        [Clear (Register "y")
        ,Val (Register "f") (-1)
        ]
    ]

rewrite :: String -> SProc
rewrite r=SProc ("#rewrite"++r) ["from","to"]
    [SAM.Alloc "test0"
    ,Copy (Memory r 0) [Register "test0"]
    ,SAM.Alloc "test1"
    ,Copy (Register "from") [Register "test1"]
    ,SAM.Alloc "flag"
    ,Inline "#isEqual" ["test0","test1","flag"]
    ,Delete "test0"
    ,Delete "test1"
    ,While (Register "flag")
        [Val (Register "flag") (-1)
        ,Clear (Memory r 0)
        ,Copy (Register "to") [Memory r 0]
        ]
    ,Delete "flag"
    ]


