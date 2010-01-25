-- | parametric variable:
--
-- * type-inference
--
-- * lambda-lifting
--
-- are done in Core language
module Core where




data CoreP=CoreP [CrData (LocHint,CrKind)] [CrProc (LocHint,CrType)]
type LocHint=String


data CrData a=CrData CrName [(CrAName a)] [(CrName,[CrAnnot a CrType])]
data CrProc a=CrProc (CrAName a) [(CrAName a)] (CrAExpr a)





{-
checkKind :: [CrData CrKind] -> Maybe [(CrName,CrKind)]
checkKind []=Just []
checkKind (CrData name vars cons)=Nothing
-}



-- | kind
data CrKind
    =CrKiApp CrKind CrKind
    |CrKiX

-- | type
data CrType
    =CrTyApp CrType CrType
    |CrTyVar CrName -- ex.: x,y,z
    |CrTyCon CrName -- ex.: #A,#L,#T,#Byte,Integer

-- | expression


data CrExpr a
    =CrLm   [CrAName a] (CrAExpr a)
    |CrApp  (CrAExpr a) (CrAExpr a)
    |CrVar  (CrAName a)
    |CrLet  Bool [(CrAName a,CrAExpr a)] (CrAExpr a) -- ^ rec?
    |CrCstr Int [CrAExpr a]
    |CrCase (CrAExpr a) [(Int,[CrAName a],CrAExpr a)]
    |CrInt  Integer
    |CrByte Int
    deriving(Show)

-- | Annotation
data CrAnnot a s=CrA a s deriving(Show)
type CrAName a=CrAnnot a CrName
type CrAExpr a=CrAnnot a (CrExpr a)

-- | 
type CrName=String



{-
123 :: Integer :: CrTyCon "Integer" :: *
(x+) :: Integer->Integer :: CrTyApp (CrTyApp (CrTyCon "#A") (CrTyCon "Integer")) (CrTyCon "Integer") :: *
#L :: * -> * :: CrKindApp CrKindAny CrKindAny

data List a=Cons a (List a)|Null


List :: * -> *

CrTyExp 
-}

-- | Core language - desugared Haskell
-- * a lot of useful transformations are done in this language

{-
data CoreP=CoreP [CrData] [CrPat] [CrDecl String]
data CoreM v=CoreM (CrExpr v)
data CoreS v=CoreS [CrDecl v] deriving(Show)

data CrData=CrData CrName [(CrName,CrType)]
data CrPat=CrPat 

type CrType=()



data CrDecl v=CrDecl CrName [v] (CrExpr v) deriving(Show)


data CrExpr v
    =CrLm   [v] (CrExpr v)
    |CrApp  (CrExpr v) (CrExpr v)
    
    |CrVar  CrName
    |CrLet  Bool [(CrName,CrExpr v)] (CrExpr v)
    -- data
    |CrCstr Int [CrExpr v]
    |CrCase (CrExpr v) [(Int,[v],CrExpr v)]
    -- literal
    |CrNum  Int
--     |CrAnnot
    deriving(Show)


type CrName=String
-}

