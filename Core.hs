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

import Util as U hiding(Pack)
import qualified Util as U
import GMachine


type CoreP=Core (LocHint,Maybe CrKind) (LocHint,Maybe CrType)
type LocHint=String


data Core a b=Core [CrData a] [CrProc b]
data CrData a=CrData CrName [(CrAName a)] [(CrName,[CrAnnot a CrType])]
data CrProc a=CrProc (CrAName a) [(CrAName a)] (CrAExpr a)





compile :: Core a b -> Process (M.Map String [GMCode])
compile (Core ds ps)=return $ M.fromList $ map (compileP m) $ ps++pds
    where
        m=M.fromList cons
        (pds,cons)=unzip $ concatMap convertData ds
        

-- | Convert one data declaration to procs and cons.
convertData :: CrData a -> [(CrProc b,(String,Int))]
convertData (CrData _ _ cs)=zipWith convertDataCon [0..] cs

-- tag, not arity
convertDataCon :: Int -> (CrName,[CrAnnot a CrType]) -> (CrProc b,(String,Int))
convertDataCon t (name,xs)=
    (CrProc (wrap name) (map wrap args) $ wrap $ CrCstr t $ map (wrap . CrVar) args,(name,t))
    where
        wrap=CrA undefined
        args=take n $ stringSeq "#d"
        n=length xs






-- | Compile one super combinator to 'GMCode'
--
-- requirement:
--
-- * must not contain lambda
--
compileP :: M.Map String Int -> CrProc a -> (String,[GMCode])
compileP mc (CrProc name args expr)=
    (unA name,F.toList $ compileE mc mv (unA expr)><S.fromList [Slide $ n+1])
    where
        n=length args
        mv=M.fromList $ zip (map unA args) (map PushArg [1..])

compileE :: M.Map String Int -> M.Map String GMCode -> CrExpr a -> S.Seq GMCode 
compileE mc mv (CrApp e0 e1)=(compileE mc mv (unA e1) >< compileE mc (shift mv 1) (unA e0)) |> MkApp
compileE mc mv (CrVar v)=S.singleton $ maybe (PushSC v) id $ M.lookup v mv
compileE mc mv (CrByte x)=S.singleton $ PushByte x
compileE mc mv (CrCstr t es)=
    concatS (zipWith (compileE mc) (map (shift mv) [0..]) (map unA $ reverse es)) |> Pack t (length es)
compileE mc mv (CrCase ec cs)=compileE mc mv (unA ec) |> Reduce RAny |> Case (map f cs)
    where
        f (con,vs,e)=(mc M.! con,F.toList $ UnPack (length vs) <| compileE mc (insMV vs) (unA e))
        insMV vs=M.union (shift mv $ length vs) $ M.fromList $ zip (map unA vs) (map Push [0..])
            -- do you need reverse $ vs here?
compileE mc mv (CrLet False bs e)=
    concatS (zipWith (compileE mc) (map (shift mv) [0..]) (map (unA . snd) $ reverse bs)) >< compileE mc mv' (unA e)
    where mv'=M.union (shift mv $ length bs) $ M.fromList $ zip (map (unA . fst) bs) (map Push [0..])
compileE mc mv (CrLet _ _ _)=error "compileE: letrec"
compileE mc mv (CrLm _ _)=error "compileE: lambda"

concatS :: [S.Seq a] -> S.Seq a
concatS=foldr (><) S.empty

shift :: M.Map String GMCode -> Int -> M.Map String GMCode
shift m d=M.map f m
    where
        f (Push n)=Push $ n+d
        f (PushArg n)=PushArg $ n+d



-- | Pretty printer for 'CoreP'
pprintCoreP :: CoreP -> String
pprintCoreP (Core ds ps)=compileSB $ U.Pack $ map (pprintData (\_ x->x)) ds++map (pprintProc (\_ x->x)) ps


pprintData :: (a -> String -> String) -> CrData a -> StrBlock
pprintData f (CrData name xs cons)=Line $ U.Pack
    [Line $ Span [Prim "data",Prim name]
    ,Indent $ U.Pack $ zipWith cv cons ("=":repeat "|")]
    where cv (name,xs) eq=Line $ Span [U.Pack [Prim eq,Prim name],Prim $ show $ length xs]

pprintProc f (CrProc n as e)=Line $ U.Pack
    [Line $ U.Pack [Span $ map (pprintAName f) $ n:as,Prim "="]
    ,Indent $ Line $ pprintAExpr f e]

pprintAExpr f (CrA ea e)=pprintExpr f e
pprintAName f (CrA na n)=Prim $ f na n

pprintExpr f (CrLm ns e)=U.Pack $
    [U.Pack [Prim "\\",Span (map (pprintAName f) ns)]
    ,U.Pack [Prim "->",pprintAExpr f e]]
pprintExpr f (CrVar x)=Prim x
pprintExpr f (CrCase e as)=U.Pack $
    [Line $ Span [Prim "case",pprintAExpr f e,Prim "of"]
    ,Indent $ U.Pack $ map cv as]
    where cv (con,vs,e)=Line $ Span [Span $ Prim con:map (pprintAName f) vs,Prim "->",pprintAExpr f e]
pprintExpr f (CrLet flag binds e)=Span $
    [Span $ (Prim $ if flag then "letrec" else "let"):map cv binds
    ,Prim "in"
    ,pprintAExpr f e]
    where cv (v,e)=U.Pack [pprintAName f v,Prim "=",pprintAExpr f e,Prim ";"]
pprintExpr f (CrApp e0 e1)=U.Pack [Prim "(",Span [pprintAExpr f e0,pprintAExpr f e1],Prim ")"]
pprintExpr f (CrByte n)=Prim $ show n
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
    |CrByte Int
    deriving(Show)

-- | Annotation
data CrAnnot a s=CrA a s deriving(Show)
type CrAName a=CrAnnot a CrName
type CrAExpr a=CrAnnot a (CrExpr a)

unA (CrA _ s)=s

-- | 
type CrName=String



