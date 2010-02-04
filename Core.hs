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
-- * dependency-analysis
--
-- * MFE-detection
--
-- * lambda lifting
--
-- are done in Core language
module Core where
import qualified Data.Foldable as F
import Data.List
import qualified Data.Map as M
import Data.Sequence((><),(|>),(<|))
import qualified Data.Sequence as S

import Util
import GMachine


type CoreP=Core (LocHint,Maybe CrKind) (LocHint,Maybe CrType)
type LocHint=String


data Core a b=Core [CrData a] [CrProc b]
data CrData a=CrData CrName [(CrAName a)] [(CrName,[CrAnnot a CrType])]
data CrProc a=CrProc (CrAName a) [(CrAName a)] (CrAExpr a)





compile :: Core a b -> Process (M.Map String [GMCode])
compile (Core ds ps)=return $ M.fromList $ map compileP $ ps++concatMap convertData ds


convertData :: CrData a -> [CrProc b]
convertData (CrData _ _ cs)=zipWith convertDataCon [0..] cs

convertDataCon :: Int -> (CrName,[CrAnnot a CrType]) -> CrProc b
convertDataCon t (name,xs)=CrProc (wrap name) (map wrap args) $ wrap $ CrCstr t $ map (wrap . CrVar) args
    where
        wrap=CrA undefined
        args=take n $ stringSeq "#d"
        n=length xs






-- | Compile one super combinator to 'GMCode'
-- requirement:
--
-- * must not contain lambda
--
compileP :: CrProc a -> (String,[GMCode])
compileP (CrProc name args expr)=
    (unA name,adjustStack $ F.toList $ compileE m (unA expr)><S.fromList [Slide $ n+1])
    where
        n=length args
        m=M.fromList $ zip (map unA args) [1..]

compileE :: M.Map String Int -> CrExpr a -> S.Seq GMCode 
compileE m (CrApp e0 e1)=(compileE m (unA e0) >< compileE m (unA e1)) |> MkApp
compileE m (CrVar v)=S.singleton $ maybe (PushSC v) Push $ M.lookup v m
compileE m (CrByte x)=S.singleton $ PushByte x
compileE m (CrCstr t es)=concatS (map (compileE m . unA) es) |> Pack t (length es)

concatS :: [S.Seq a] -> S.Seq a
concatS=foldr (><) S.empty


adjustStack :: [GMCode] -> [GMCode]
adjustStack=aux 0
    where
        aux d []=[]
        aux d (Push n:cs)=Push (d+n):aux (d+1) cs
        aux d (MkApp:cs)=MkApp:aux (d-1) cs
        aux d (PushSC k:cs)=PushSC k:aux (d+1) cs
        aux d (PushByte x:cs)=PushByte x:aux (d+1) cs
        aux d (Slide n:cs)=Slide n:aux (d-n) cs
        aux d (Alloc n:cs)=Alloc n:aux (d-n+1) cs
        aux d (Pack t n:cs)=Pack t n:aux (d-n+1) cs






-- | Pretty printer for 'CoreP'
pprintCoreP :: CoreP -> String
pprintCoreP (Core ds ps)=compileSB 0 $
    map (pprintData (\_ x->x)) ds++map (pprintProc (\_ x->x)) ps


pprintData :: (a -> String -> String) -> CrData a -> StrBlock
pprintData f (CrData name xs cons)=SBlock $
    [SBlock [SPrim "data",SSpace,SPrim name]
    ,SIndent
    ,SNewline
    ,SBlock $ zipWith f cons ("=":repeat "|")
    ,SDedent
    ,SNewline
    ]
    where f (name,xs) eq=SBlock [SPrim eq,SPrim name,SSpace,SPrim $ show $ length xs,SNewline]

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
pprintExpr f (CrByte n)=SPrim $ show n
-- pprintExpr f (Cr
pprintExpr f e=error $ "pprintExpr:"++show e






{-
checkKind :: [CrData CrKind] -> Maybe [(CrName,CrKind)]
checkKind []=Just []
checkKind (CrData name vars cons)=Nothing
-}



-- | kind
data CrKind
    =CrKiApp CrKind CrKind -- ^ left associative application of types
    |CrKiX -- ^ the kind of proper types, /*/

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

unA (CrA _ s)=s

-- | 
type CrName=String



