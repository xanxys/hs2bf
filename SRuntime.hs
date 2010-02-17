module SRuntime where
import SAM

appTag=0
scTag=1
constTag=2
structTag=3


library=
    [stack1,stackNew,stackTop
    ,heap1,heapNew,heapNew_,heapTop,heapRef
    ,gc,gcTransfer,gcMark,gcCopy,gcIndex,gcRewrite
    ,rootProc,setupMemory,mainLoop,eval,evalApp,evalSC,evalStr,evalE
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
    [SAM.Alloc "sc" -- 0:halt 1:cont-eval *:exec
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
    [Inline "#stack1" []
    ,Inline "#stackTop" []
    ,SAM.Alloc "addr"
    ,Copy (Memory "S0" 0) [Register "addr"]
    ,Inline "#stack1" []
    ,Inline "#heapRef" ["addr"]
    ,Delete "addr"
    ,SAM.Alloc "tag"
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
    [SAM.Alloc "addr"
    ,Copy (Memory "Hp" 3) [Register "addr"]
    ,Inline "#heap1" []
    ,Inline "#stackNew" []
    ,Move (Register "addr") [Memory "S0" 0]
    ,Delete "addr"
    ,Inline "#stack1" []
    ]

evalSC=SProc "%evalSC" ["sc"]
    [Val (Register "sc") (-1)
    ,Copy (Memory "Hp" 3) [Register "sc"]
    ,Inline "#heap1" []
    ]


evalStr=SProc "%evalStr" ["sc"]
    [Inline "#heap1" []
    ,Inline "#stackTop" []
    ,SAM.Alloc "root"
    ,Val (Register "root") 1
    ,While (Memory "S0" (-1)) -- non-root frame -> get sc
        [Val (Register "sc") (-1) -- sc:=0
        ,Val (Register "root") (-1)
        ,SAM.Alloc "addr"
        ,Move (Memory "S0" (-1)) [Register "addr"]
        ,Move (Memory "S0" 0) [Memory "S0" (-1)] -- move exp to top
        ,Locate (-1)
        ,Inline "#stack1" []
        ,Inline "#heapRef" ["addr"]
        ,Delete "addr"
        ,Copy (Memory "Hp" 3) [Register "sc"]
        ,Inline "#heap1" []
        ]
    ,While (Register "root")
        [Val (Register "root") (-1)
        ,Inline "#stackTop" []
        ,SAM.Alloc "addr"
        ,Copy (Memory "S0" 0) [Register "addr"]
        ,Inline "#stack1" []
        ,Inline "#heapRef" ["addr"]
        ,Delete "addr"
        ,Inline "%evalE" ["sc"]
        ]
    ,Delete "root"
    ]

-- sc must be 1 on entry
evalE=SProc "%evalE" ["sc"]
    [SAM.Alloc "stag"
    ,Copy (Memory "Hp" 3) [Register "stag"]
    ,Dispatch "stag"
        [(0, -- input f
            [SAM.Alloc "faddr"
            ,Copy (Memory "Hp" 4) [Register "faddr"]
            -- construct app frame: [7,gcTag,appTag,f,aaddr+1,aaddr,7]
            ,SAM.Alloc "aaddr"
            ,Inline "#heapNew" ["aaddr"]
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
            ,Inline "#heap1" []
            ,Inline "#stackTop" []
            ,Clear (Memory "S0" 0)
            ,Move (Register "aaddr") [Memory "S0" 0]
            ,Delete "aaddr"
            ,Inline "#stack1" []
            ])
        ,(1, -- output x k [8,gcTag,structTag,1,X,K,addr,8]
            [SAM.Alloc "xaddr"
            ,SAM.Alloc "kaddr"
            ,Copy (Memory "Hp" 4) [Register "xaddr"]
            ,Copy (Memory "Hp" 5) [Register "kaddr"]
            -- refer and output x
            ,Inline "#heap1" []
            ,Inline "#heapRef" ["xaddr"]
            ,Delete "xaddr"
            ,Output (Memory "Hp" 3)
            -- replace stack top
            ,Inline "#heap1" []
            ,Inline "#stackTop" []
            ,Clear (Memory "S0" 0)
            ,Move (Register "kaddr") [Memory "S0" 0]
            ,Delete "kaddr"
            ,Inline "#stack1" []
            ])
        ,(2, -- halt
            [Val (Register "sc") (-1) -- sc:=0
            ,Inline "#heap1" []
            ,Inline "#stackTop" []
            ,Clear (Memory "S0" 0)
            ])
        ]
    ,Delete "stag"
    ]

-- | Must be on address 1. /sc/ will be 1 or 0.
exec :: [(String,Int)] -> SProc
exec xs=SProc "%exec" ["sc"]
    [SAM.Alloc "cont"
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



-- | Return to address 1. Must be aligned with a heap frame.
heap1 :: SProc
heap1=SProc "#heap1" []
    [While (Memory "Hp" (-1))
        [SAM.Alloc "cnt"
        ,Copy (Memory "Hp" (-1)) [Register "cnt"]
        ,While (Register "cnt")
            [Val (Register "cnt") (-1)
            ,Locate (-1)
            ]
        ,Delete "cnt"
        ]
    ]

-- | Move to where a new heap frame would be and write the address to addr. Must be aligned with frame.
-- The first size field is 0, but others are undefined.
heapNew :: SProc
heapNew=SProc "#heapNew" ["addr"]
    [While (Memory "Hp" 0)
        [SAM.Alloc "cnt"
        ,Copy (Memory "Hp" 0) [Register "cnt"]
        ,While (Register "cnt")
            [Val (Register "cnt") (-1)
            ,Locate 1]
        ,Delete "cnt"
        ]
    ,Copy (Memory "Hp" (-2)) [Register "addr"]
    ,Val (Register "addr") 1
    ]

-- | Move to where a new heap frame would be. Must be aligned with frame.
-- The first size field is 0, but others are undefined.
heapNew_ :: SProc
heapNew_=SProc "#heapNew_" []
    [While (Memory "Hp" 0)
        [SAM.Alloc "cnt"
        ,Copy (Memory "Hp" 0) [Register "cnt"]
        ,While (Register "cnt")
            [Val (Register "cnt") (-1)
            ,Locate 1]
        ,Delete "cnt"
        ]
    ]

-- | Move to where the heap top. Must be aligned with frame.
heapTop :: SProc
heapTop=SProc "#heapTop" []
    [While (Memory "Hp" 0)
        [SAM.Alloc "cnt"
        ,Copy (Memory "Hp" 0) [Register "cnt"]
        ,While (Register "cnt")
            [Val (Register "cnt") (-1)
            ,Locate 1]
        ,Delete "cnt"
        ]
    ,SAM.Alloc "cnt"
    ,Copy (Memory "Hp" (-1)) [Register "cnt"]
    ,While (Register "cnt")
        [Val (Register "cnt") (-1)
        ,Locate (-1)
        ]
    ,Delete "cnt"
    ]

-- | Move to the frame pointed by addr. addr will be 0. Must be aligned.
heapRef :: SProc
heapRef=SProc "#heapRef" ["addr"]
    [Val (Register "addr") (-1)
    ,While (Register "addr")
        [Val (Register "addr") (-1)
        ,SAM.Alloc "cnt"
        ,Copy (Memory "Hp" 0) [Register "cnt"]
        ,While (Register "cnt")
            [Val (Register "cnt") (-1)
            ,Locate 1
            ]
        ,Delete "cnt"
        ]
    ]

-- | Return to address 1. Must be on stack($S\/=0).
stack1 :: SProc
stack1=SProc "#stack1" []
    [While (Memory "S0" 0) [Locate (-1)],Locate 1]

-- | Move to stack new.
stackNew :: SProc
stackNew=SProc "#stackNew" []
    [While (Memory "S0" 0) [Locate 1]]

-- | Move to stack top.
stackTop :: SProc
stackTop=SProc "#stackTop" []
    [While (Memory "S0" 0) [Locate 1]
    ,Locate (-1)
    ]


gc :: SProc
gc=SProc "#gc" []
    [Inline "#gcTransfer" []
    ,Inline "#gcMark" []
    ,Inline "#gcCopy" []
    ,Inline "#gcIndex" []
    ,Inline "#gcRewrite" []
    ]

gcTransfer :: SProc
gcTransfer=SProc "#gcTransfer" []
    []

gcMark :: SProc
gcMark=SProc "#gcMark" []
    []

gcCopy :: SProc
gcCopy=SProc "#gcCopy" []
    []

gcIndex :: SProc
gcIndex=SProc "#gcIndex" []
    []

gcRewrite :: SProc
gcRewrite=SProc "#gcRewrite" []
    []

