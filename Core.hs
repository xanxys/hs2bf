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
import Control.Arrow
import Data.Ord
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Foldable as F
import Data.Sequence((><),(|>),(<|))
import qualified Data.Sequence as Q

import Util as U hiding(Pack)
import qualified Util as U
import GMachine


type LocHint=String


data Core=Core [CrData] [CrProc]
data CrData=CrData CrName [CrName] [(CrName,[CrType])]
data CrProc=CrProc CrName [CrName] CrExpr





compile :: Core -> Process (M.Map String [GMCode])
compile (Core ds ps)=return $ M.fromList $ undef:map (compileP m) (ps++pds)
    where
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



-- | Resolve "" in 'Case'
simplify :: Core -> Process Core
simplify (Core ds ps)=return $ Core ds $ map (smplP table) ps
    where
        table=M.fromList $ concatMap (mkP . map snd) $ groupBy (equaling fst) $ concatMap conCT ds
        mkP xs=map (\x->(fst x,S.fromList xs)) xs

conCT :: CrData -> [(CrName,(CrName,Int))]
conCT (CrData n _ xs)=zip (repeat n) (map (second length) xs)

smplP :: M.Map String (S.Set (String,Int)) -> CrProc -> CrProc
smplP t (CrProc name args expr)=CrProc name args $ smplE t expr

smplE :: M.Map String (S.Set (String,Int)) -> CrExpr -> CrExpr
smplE t (CrApp e0 e1)=CrApp (smplE t e0) (smplE t e1)
smplE t (CrCstr tag es)=CrCstr tag $ map (smplE t) es
smplE t (CrLet f bs e)=CrLet f (map (second $ smplE t) bs) $ smplE t e
smplE t (CrLm vs e)=CrLm vs $ smplE t e
smplE t (CrCase ec cs)
    |null cocs      = CrCase (smplE t ec) $ nrmcons
    |length cocs==1 = CrCase (smplE t ec) $ cocons (thr3 $ head cocs)++nrmcons
    |otherwise      = error "smplE: more than 2 defaults!"
    where
        (cocs,nrmcs)=partition (null . fst3) cs
        
        nrmcons=map (\(x,y,z)->(x,y,smplE t z)) nrmcs
        cocons x=map (\(c,n)->(c,replicate n "",smplE t x)) $ F.toList s
        s=S.difference (t M.! (fst $ head cons)) (S.fromList cons)
        cons=filter (not . null . fst) $ map (\(x,y,_)->(x,length y)) cs
smplE t x=x
    


-- | Compile one super combinator to 'GMCode'
--
-- requirement:
--
-- * must not contain lambda
--
compileP :: M.Map String Int -> CrProc -> (String,[GMCode])
compileP mc (CrProc name args expr)=
    (name,F.toList $ compileE mc mv expr><Q.fromList [Slide $ n+1])
    where
        n=length args
        mv=M.fromList $ zip args (map PushArg [1..])

compileE :: M.Map String Int -> M.Map String GMCode -> CrExpr -> Q.Seq GMCode 
compileE mc mv (CrApp e0 e1)=(compileE mc mv e1 >< compileE mc (shift mv 1) e0) |> MkApp
compileE mc mv (CrVar v)=Q.singleton $ maybe (PushSC v) id $ M.lookup v mv
compileE mc mv (CrByte x)=Q.singleton $ PushByte x
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

concatS :: [Q.Seq a] -> Q.Seq a
concatS=foldr (><) Q.empty

shift :: M.Map String GMCode -> Int -> M.Map String GMCode
shift m d=M.map f m
    where
        f (Push n)=Push $ n+d
        f (PushArg n)=PushArg $ n+d



-- | Pretty printer for 'Core'
pprint :: Core -> String
pprint (Core ds ps)=compileSB $ U.Pack $ map pprintData ds++map pprintProc ps


pprintData :: CrData -> StrBlock
pprintData (CrData name xs cons)=Line $ U.Pack
    [Line $ Span [Prim "data",Prim name]
    ,Indent $ U.Pack $ zipWith cv cons ("=":repeat "|")]
    where cv (name,xs) eq=Line $ Span [U.Pack [Prim eq,Prim name],Prim $ show $ length xs]

pprintProc (CrProc n as e)=Line $ U.Pack
    [Line $ U.Pack [Span $ map pprintName $ n:as,Prim "="]
    ,Line $ Indent $ pprintExpr e]

pprintName :: CrName -> StrBlock
pprintName n=Prim n


pprintExpr :: CrExpr -> StrBlock
pprintExpr (CrCase e as)=U.Pack $
    [Line $ Span [Prim "case",pprintExprInline e,Prim "of"]
    ,Indent $ U.Pack $ map cv as]
    where
        cv (con,vs,e)=U.Pack [Line $ Span $ Prim con:map pprintName vs++[Prim "->"],Indent $ pprintExpr e]
pprintExpr (CrLet flag binds e)=U.Pack $
    [Line $ Prim $ if flag then "letrec" else "let"
    ,Indent $ U.Pack $ map cv binds
    ,Line $ Prim "in"
    ,Indent $ pprintExpr e]
    where cv (v,e)=Line $ Span [pprintName v,Prim "=",pprintExprInline e]
pprintExpr x=Line $ pprintExprInline x


pprintExprInline :: CrExpr -> StrBlock
pprintExprInline (CrLm ns e)=U.Pack $
    [U.Pack [Prim "\\",Span (map pprintName ns)]
    ,U.Pack [Prim "->",pprintExpr e]]
pprintExprInline (CrVar x)=Prim x
pprintExprInline (CrCase e as)=Span $
    [Span [Prim "case",pprintExpr e,Prim "of"],Span $ map cv as]
    where
        cv (con,vs,e)=Span [Span $ Prim con:map pprintName vs,Prim "->",pprintExprInline e,Prim ";"]
pprintExprInline (CrLet flag binds e)=Span $
    [Span $ (Prim $ if flag then "letrec" else "let"):map cv binds
    ,Prim "in"
    ,pprintExprInline e]
    where cv (v,e)=U.Pack [pprintName v,Prim "=",pprintExpr e,Prim ";"]
pprintExprInline (CrApp e0 e1)=U.Pack [Prim "(",Span [pprintExprInline e0,pprintExprInline e1],Prim ")"]
pprintExprInline (CrByte n)=Prim $ show n
-- pprintExpr f (Cr
pprintExprInline e=error $ "pprintExprInline:"++show e






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



