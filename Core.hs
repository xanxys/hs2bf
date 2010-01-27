-- | parametric variable:
--    Partially type-annotated
-- * kind-inference -> possible kind error
--    Fully-kind-annotated -> throw away kind
-- * type-inference -> possible type error
--    Fully-type-annotated
-- * throw away LocHint
--
-- * type-inference
--
-- * lambda-lifting
--
-- are done in Core language
module Core where
import Data.List


type CoreP=Core (LocHint,Maybe CrKind) (LocHint,Maybe CrType)
type LocHint=String


data Core a b=Core [CrData a] [CrProc b]
data CrData a=CrData CrName [(CrAName a)] [(CrName,[CrAnnot a CrType])]
data CrProc a=CrProc (CrAName a) [(CrAName a)] (CrAExpr a)


-- | Pretty printer for 'CoreP'
pprintCoreP :: CoreP -> String
pprintCoreP (Core ds ps)=compileSB 0 $
    map (pprintData (\_ x->x)) ds++map (pprintProc (\_ x->x)) ps

compileSB :: Int -> [StrBlock] -> String
compileSB _ []=""
compileSB n ((SBlock ss):xs)=compileSB n $ ss++xs
compileSB n ((SPrim s):xs)=s++compileSB n xs
compileSB n (SSpace:xs)=" "++compileSB n xs
compileSB n (SNewline:xs)="\n"++replicate (n*4) ' '++compileSB n xs
compileSB n (SIndent:xs)=compileSB (n+1) xs
compileSB n (SDedent:xs)=compileSB (n-1) xs

data StrBlock
    =SBlock [StrBlock]
    |SPrim String
    |SSpace
    |SNewline
    |SIndent
    |SDedent

pprintData :: (a -> String -> String) -> CrData a -> StrBlock
pprintData f _=SPrim "SARX SARK / ELDA TALUTA / ARK ARX"

pprintProc f (CrProc n as e)=SBlock $
    (intersperse SSpace $ map (pprintAName f) $ n:as)++
    [SPrim "=",SIndent,SNewline,pprintAExpr f e,SDedent,SNewline]

pprintAExpr f (CrA ea e)=pprintExpr f e
pprintAName f (CrA na n)=SPrim $ f na n

pprintExpr f (CrLm ns e)=SBlock $ SPrim "\\":intersperse SSpace (map (pprintAName f) ns)++
    [SPrim "->",pprintAExpr f e]
pprintExpr f (CrVar x)=SPrim x
pprintExpr f (CrCase e as)=SBlock $
    [SPrim "case",SSpace,pprintAExpr f e,SSpace,SPrim "of",SIndent,SNewline]++map cv as++[SDedent]
    where cv (con,vs,e)=SBlock $ intersperse SSpace $ SPrim con:map (pprintAName f) vs++[SPrim "->",pprintAExpr f e]
pprintExpr f (CrLet flag binds e)=SBlock $ (SPrim $ if flag then "letrec" else "let"):SSpace:map cv binds++
    [SSpace,SPrim "in",SSpace,pprintAExpr f e]
    where cv (v,e)=SBlock [pprintAName f v,SPrim "=",pprintAExpr f e]
pprintExpr f (CrApp e0 e1)=SBlock [SPrim "(",pprintAExpr f e0,SSpace,pprintAExpr f e1,SPrim ")"]
pprintExpr f (CrInt n)=SPrim $ show n
-- pprintExpr f (Cr
pprintExpr f e=error $ "pprintExpr:"++show e






{-
checkKind :: [CrData CrKind] -> Maybe [(CrName,CrKind)]
checkKind []=Just []
checkKind (CrData name vars cons)=Nothing
-}



-- | kind
data CrKind
    =CrKiApp CrKind CrKind
    |CrKiX

instance Show CrKind where
    show (CrKiApp k0 k1)="("++show k0++") -> ("++show k1++")"
    show CrKiX="*"

-- | type
data CrType
    =CrTyApp CrType CrType
    |CrTyVar CrName -- ex.: x,y,z
    |CrTyCon CrName -- ex.: #A,#L,#T,#Byte,Integer

instance Show CrType where
    show (CrTyApp t0 t1)="("++show t0++") -> ("++show t1++")"
    show (CrTyVar x)=x
    show (CrTyCon x)=x

-- | expression
data CrExpr a
    =CrLm   [CrAName a] (CrAExpr a)
    |CrApp  (CrAExpr a) (CrAExpr a)
    |CrLet  Bool [(CrAName a,CrAExpr a)] (CrAExpr a) -- ^ rec?
    |CrCstr Int [CrAExpr a]
    |CrCase (CrAExpr a) [(String,[CrAName a],CrAExpr a)]
    |CrVar  CrName
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

