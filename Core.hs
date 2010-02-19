-- | parametric variable:
--    Partially type-annotated
-- * kind-inference -> possible kind error
--    Fully-kind-annotated -> throw away kind
-- * type-inference -> possible type error
--    Fully-type-annotated
--
-- * type-inference
--
-- * uniquify
--
-- * dependency-analysis(convert letrec to let)
--
-- * MFE-detection
--
-- * lambda lifting
--
-- are done in Core language
module Core where
import Control.Arrow
import Control.Monad.Writer
import Data.Ord
import Data.Char
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
data CrData=CrData CrName [CrName] [(CrName,[CrType])] deriving(Show)
data CrProc=CrProc CrName [CrName] CrExpr deriving(Show)





-- | Rename all variables to be unique in each 'CrProc'.
uniquify :: Core -> Core
uniquify (Core ds ps)=Core ds $ map (uniquifyP m0 r0) ps
    where
        r0=""
        m0=M.fromList $ zip gs gs
        gs=concatMap (\(CrData _ _ cons)->map fst cons) ds++map (\(CrProc n _ _)->n) ps

uniquifyP :: M.Map CrName CrName -> String -> CrProc -> CrProc
uniquifyP m r (CrProc n as e)=CrProc n (map (m' M.!) as) $ uniquifyE m' r e
    where m'=bind r m as

uniquifyE :: M.Map CrName CrName -> String -> CrExpr -> CrExpr
uniquifyE m r (CrVar v)=CrVar $ m M.! v
uniquifyE m r (CrApp e0 e1)=CrApp (uniquifyE m n1 e0) (uniquifyE m n2 e1)
    where [n1,n2]=branch 2 r
uniquifyE m r (CrCstr t es)=CrCstr t $ zipWith (uniquifyE m) ns es
    where ns=branch (length es) r
uniquifyE m r (CrCase e cs)=CrCase (uniquifyE m n e) (zipWith f cs ns)
    where
        n:ns=branch (length cs+1) r
        f (tag,vs,e) n=let m'=bind r m vs in (tag,map (m' M.!) vs,uniquifyE m' n e)
uniquifyE m r (CrLet flag bs e)=CrLet flag (zipWith f bs ns) (uniquifyE m' n e)
    where
        m'=bind r m $ map fst bs
        n:ns=branch (length bs+1) r
        f (v,e) n=(m' M.! v,uniquifyE (if flag then m' else m) n e)
uniquifyE m r (CrLm vs e)=CrLm (map (m' M.!) vs) $ uniquifyE m' r e
    where m'=bind r m vs
uniquifyE m r e@(CrByte _)=e

branch :: Int -> String -> [String]
branch n r=map ((r++) . (:[])) ss
    where ss=take n $ iterate succ 'a'

bind :: String -> M.Map CrName CrName -> [CrName] -> M.Map CrName CrName
bind r m vs=M.union (M.fromList $ zip vs vs') m
    where vs'=map ((++r) . (++"_")) vs


        




liftLambdaW :: Core -> Core
liftLambdaW (Core ds ps)=Core ds $ concatMap liftLambda ps


liftLambda :: CrProc -> [CrProc]
liftLambda (CrProc n args e)=CrProc n args e':ps
    where (e',ps)=runWriter (liftl ("_l_"++n) e)


liftl :: String -> CrExpr -> Writer [CrProc] CrExpr
liftl n e0@(CrLm as e)=do
    liftl (n++"_") e >>= post . CrProc n (fvs++as)
    return $! multiApp (CrVar n) $ map CrVar fvs
    where fvs=S.toList $ S.filter (not . isUpper . head) $ freeVar e0
liftl n (CrLet flag bs e)=liftM2 (CrLet flag) (mapM f bs) (liftl (n++"_") e)
    where f (v,e)=liftM (\x->(v,x)) $ liftl (n++"_"++v) e
liftl n (CrCase e cs)=liftM2 CrCase (liftl (n++"_") e) (mapM f cs)
    where f (t,vs,e)=liftM (\x->(t,vs,x)) $ liftl (n++"_"++t) e
liftl n (CrApp e0 e1)=liftM2 CrApp (liftl n e0) (liftl (n++"_") e1)
liftl n (CrCstr tag es)=liftM (CrCstr tag) (zipWithM f es [0..])
    where f e k=liftl (n++"_"++show k) e
liftl n e=return e

post :: a -> Writer [a] ()
post=tell . (:[])


freeVar :: CrExpr -> S.Set CrName
freeVar e=collectV e `S.difference` collectB e

collectB :: CrExpr -> S.Set CrName
collectB (CrApp e0 e1)=collectB e0 `S.union` collectB e1
collectB (CrLet _ bs e)=S.fromList (map fst bs) `S.union` (S.unions $ map collectB $ e:map snd bs)
collectB (CrCase e cs)=S.fromList (concatMap snd3 cs) `S.union` (S.unions $ map collectB $ e:map thr3 cs)
collectB (CrLm as e)=S.fromList as `S.union` collectB e
collectB _=S.empty

collectV :: CrExpr -> S.Set CrName
collectV (CrVar x)=S.singleton x
collectV (CrApp e0 e1)=collectV e0 `S.union` collectV e1
collectV (CrLet _ bs e)=S.unions $ map collectV $ e:map snd bs
collectV (CrCase e cs)=S.unions $ map collectV $ e:map thr3 cs
collectV (CrLm as e)=collectV e




multiApp :: CrExpr -> [CrExpr] -> CrExpr
multiApp=foldl CrApp








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



-- | Resolve default clause in 'Case' and 'uniquify'.
simplify :: Core -> Process Core
simplify (Core ds ps)=return $ liftLambdaW $ uniquify $ Core ds $ map (smplP table) ps
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
        f (con,vs,e)=(M.findWithDefault (error $ "cE:not found:"++con) con mc
                     ,F.toList $
                            (UnPack (length vs) <|
                            compileE mc (insMV $ reverse vs) e) |>
                            Slide (length vs)
                     ) 
        insMV vs=M.union (M.fromList $ zip vs (map Push [0..])) $ shift mv $ length vs
compileE mc mv (CrLet False bs e)=
    concatS (zipWith (compileE mc) (map (shift mv) [0..]) (map snd $ reverse bs)) ><
    compileE mc mv' e ><
    Q.fromList [Slide $ length bs]
    where
        mv'=M.union (M.fromList $ zip (map fst bs) (map Push [0..])) $ shift mv $ length bs
compileE mc mv (CrLet _ _ _)=error "compileE: letrec"
compileE mc mv (CrLm _ _)=error "compileE: lambda must be lifted beforehand"

concatS :: [Q.Seq a] -> Q.Seq a
concatS=foldr (><) Q.empty

shift :: M.Map String GMCode -> Int -> M.Map String GMCode
shift m d=M.map f m
    where
        f (Push n)=Push $ n+d
        f (PushArg n)=PushArg $ n+d



-- | Pretty printer for 'Core'
pprint :: Core -> String
pprint (Core ds ps)=compileSB $ Group $ intersperse EmptyLine $ map pprintData ds++map pprintProc ps


pprintData :: CrData -> SBlock
pprintData (CrData name xs cons)=Group
    [Line $ Span [Prim "data",Prim name]
    ,Indent $ Group $ zipWith cv cons ("=":repeat "|")]
    where cv (name,xs) eq=Line $ Span [U.Pack [Prim eq,Prim name],Prim $ show $ length xs]

pprintProc :: CrProc -> SBlock
pprintProc (CrProc n as e)=Group
    [Line $ U.Pack [Span $ map Prim $ n:as,Prim "="]
    ,Indent $ pprintExpr e]

pprintExpr :: CrExpr -> SBlock
pprintExpr (CrCase e as)=Group
    [Line $ Span [Prim "case",pprintExprI e,Prim "of"]
    ,Indent $ Group $ map cv as]
    where
        cv (con,vs,e)=Group [Line $ Span $ Prim con:map Prim vs++[Prim "->"],Indent $ pprintExpr e]
pprintExpr (CrLet flag binds e)=Group
    [Line $ Prim $ if flag then "letrec" else "let"
    ,Indent $ Group $ map (\(v,e)->Line $ Span [Prim v,Prim "=",pprintExprI e]) binds
    ,Line $ Prim "in"
    ,Indent $ pprintExpr e]
pprintExpr x=Line $ pprintExprI x


pprintExprI :: CrExpr -> IBlock
pprintExprI (CrLm ns e)=U.Pack $
    [U.Pack [Prim "\\",Span $ map Prim ns]
    ,U.Pack [Prim "->",pprintExprI e]]
pprintExprI (CrVar x)=Prim x
pprintExprI (CrCase e as)=Span $
    [Span [Prim "case",pprintExprI e,Prim "of"],Span $ map cv as]
    where
        cv (con,vs,e)=Span [Span $ Prim con:map Prim vs,Prim "->",pprintExprI e,Prim ";"]
pprintExprI (CrLet flag binds e)=Span $
    [Span $ (Prim $ if flag then "letrec" else "let"):map cv binds
    ,Prim "in"
    ,pprintExprI e]
    where cv (v,e)=U.Pack [Prim v,Prim "=",pprintExprI e,Prim ";"]
pprintExprI (CrApp e0 e1)=U.Pack [Prim "(",Span [pprintExprI e0,pprintExprI e1],Prim ")"]
pprintExprI (CrByte n)=Prim $ show n
-- pprintExpr f (Cr
pprintExprI e=error $ "pprintExprI:"++show e






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



