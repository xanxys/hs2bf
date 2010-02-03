module Error where

data CompileError=CompileError
    String -- ^ corresponding part of program (ex.: frontend, core)
    String -- ^ position (inline)
    String -- ^ error (multiple line)

instance Show CompileError where
    show (CompileError m p d)=m++":"++p++"\n"++d

