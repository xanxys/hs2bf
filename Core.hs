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


type LocHint=String


data Core=Core [CrData] [CrProc]
data CrData=CrData CrName [CrName] [(CrName,[CrType])]
data CrProc=CrProc CrName [CrName] CrExpr





compile :: Core -> Process (M.Map String [GMCode])
compile core=return $ M.fromList $ undef:map (compileP m) (ps++pds)
    where
        Core ds ps=Core.simplify core
        m=M.fromList cons
        (pds,cons)=unzip $ concatMap convertData ds
        undef=("undefined",[UError "undefined"])


-- | Convert one data declaration to procs and cons.
convertData :: CrData -> [(CrProc,(String,Int))]
convertData (CrData _ _ cs)=zipWith convertDataCon [0..] cs

-- tag, not arity
convertDataCon :: Int -> (CrName,[CrType]) -> (CrProc,(String,Int))
convertDataCon t (name,xs)=
    (CrProc name args $ CrCstr t $ map CrVar args,(name,t))
    where
        args=take n $ stringSeq "#d"
        n=length xs



-- | Resolve _ in 'Case'
simplify :: Core -> Core
simplify (Core ds ps)=Core ds ps'
    where ps'=ps
    


-- | Compile one super combinator to 'GMCode'
--
-- requirement:
--
-- * must not contain lambda
--
compileP :: M.Map String Int -> CrProc -> (String,[GMCode])
compileP mc (CrProc name args expr)=
    (name,F.toList $ compileE mc mv expr><S.fromList [Slide $ n+1])
    where
        n=length args
        mv=M.fromList $ zip args (map PushArg [1..])

compileE :: M.Map String Int -> M.Map String GMCode -> CrExpr -> S.Seq GMCode 
compileE mc mv (CrApp e0 e1)=(compileE mc mv e1 >< compileE mc (shift mv 1) e0) |> MkApp
compileE mc mv (CrVar v)=S.singleton $ maybe (PushSC v) id $ M.lookup v mv
compileE mc mv (CrByte x)=S.singleton $ PushByte x
compileE mc mv (CrCstr t es)=
    concatS (zipWith (compileE mc) (map (shift mv) [0..]) (reverse es)) |> Pack t (length es)
compileE mc mv (CrCase ec cs)=compileE mc mv ec |> Reduce RAny |> Case (map f cs)
    where
        f (con,vs,e)=(M.findWithDefault (error $ "cE:not found:"++con) con mc,F.toList $ UnPack (length vs) <| compileE mc (insMV vs) e)
        insMV vs=M.union (shift mv $ length vs) $ M.fromList $ zip vs (map Push [0..])
            -- do you need reverse $ vs here?
compileE mc mv (CrLet False bs e)=
    concatS (zipWith (compileE mc) (map (shift mv) [0..]) (map snd $ reverse bs)) >< compileE mc mv' e
    where mv'=M.union (shift mv $ length bs) $ M.fromList $ zip (map fst bs) (map Push [0..])
compileE mc mv (CrLet _ _ _)=error "compileE: letrec"
compileE mc mv (CrLm _ _)=error "compileE: lambda"

concatS :: [S.Seq a] -> S.Seq a
concatS=foldr (><) S.empty

shift :: M.Map String GMCode -> Int -> M.Map String GMCode
shift m d=M.map f m
    where
        f (Push n)=Push $ n+d
        f (PushArg n)=PushArg $ n+d



-- | Pretty printer for 'Core'
pprintCore :: Core -> String
pprintCore (Core ds ps)=compileSB $ U.Pack $ map pprintData ds++map pprintProc ps


pprintData :: CrData -> StrBlock
pprintData (CrData name xs cons)=Line $ U.Pack
    [Line $ Span [Prim "data",Prim name]
    ,Indent $ U.Pack $ zipWith cv cons ("=":repeat "|")]
    where cv (name,xs) eq=Line $ Span [U.Pack [Prim eq,Prim name],Prim $ show $ length xs]

pprintProc (CrProc n as e)=Line $ U.Pack
    [Line $ U.Pack [Span $ map pprintName $ n:as,Prim "="]
    ,Indent $ Line $ pprintExpr e]

pprintName n=Prim n

pprintExpr (CrLm ns e)=U.Pack $
    [U.Pack [Prim "\\",Span (map pprintName ns)]
    ,U.Pack [Prim "->",pprintExpr e]]
pprintExpr (CrVar x)=Prim x
pprintExpr (CrCase e as)=U.Pack $
    [Line $ Span [Prim "case",pprintExpr e,Prim "of"]
    ,Indent $ U.Pack $ map cv as]
    where
        cv0 (v,e)=[Line $ Span [pprintName v,Prim "->",pprintExpr e]]
        cv (con,vs,e)=Line $ Span [Span $ Prim con:map pprintName vs,Prim "->",pprintExpr e]
pprintExpr (CrLet flag binds e)=Span $
    [Span $ (Prim $ if flag then "letrec" else "let"):map cv binds
    ,Prim "in"
    ,pprintExpr e]
    where cv (v,e)=U.Pack [pprintName v,Prim "=",pprintExpr e,Prim ";"]
pprintExpr (CrApp e0 e1)=U.Pack [Prim "(",Span [pprintExpr e0,pprintExpr e1],Prim ")"]
pprintExpr (CrByte n)=Prim $ show n
-- pprintExpr f (Cr
pprintExpr e=error $ "pprintExpr:"++show e






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
data CrExpr
    =CrLm   [CrName] CrExpr
    |CrApp  CrExpr CrExpr
    |CrLet  Bool [(CrName,CrExpr)] CrExpr -- ^ rec?
    |CrCstr Int [CrExpr]
    |CrCase CrExpr [(String,[CrName],CrExpr)]
    |CrVar  CrName
    |CrByte Int
    deriving(Show)


-- | identifier
type CrName=String



