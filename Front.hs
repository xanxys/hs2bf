-- | Frontend: Haskell -> 'CoreP' desugarer
--
-- design policy: minimize the amount of code
--
-- [0. 'collectModules' :: IO \[Hs\]]
--   Parse necesarry modules.
--
-- [1. 'WeakDesugar' :: Hs -> Hs]
--   Shallow desugaring (including unguarding, if removal)
--
-- [2. 'MidDesugar' :: Hs -> Hs]
--   A little bit deep desugaring (where -> let, pattern(PatBind,Lambda) -> case, merge FunBinds)
--   Introduces dummy variables
--
-- [3. 'mergeModules' :: \[Hs\] -> Hs]
--   Resolve all name references and make them 'UnQual'.
--   Unknown identifiers are detected in this process.
--
-- [4. 'sds' :: Hs -> 'CoreP']
--   Explicit pattern matching
--
-- Dummy variable naming convention:
--
-- * #aa_2... : arguments ('HsMatch')
--
-- * #xa_1... : pattern matching
module Front where
import Control.Arrow
import Control.Exception
import Control.Monad
import Control.Monad.Error
import Data.Char
import Data.Either
import Data.List
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Language.Haskell.Parser
import Language.Haskell.Syntax
import System.Directory
import System.FilePath.Posix

import Util
import Core hiding(multiApp)


-- | Necessary information for translating module name to 'FilePath'.
data ModuleEnv=ModuleEnv [FilePath]

compile :: [HsModule] -> Process Core
compile ms=return $ sds $ mergeModules $ map (mds . wds) ms

-- | Search all necesarry modules and parse them all (if possible).
-- If an parser error occurs, parse as many other files as possible to report further errors.
collectModules :: ModuleEnv -> String -> IO (Process [HsModule])
collectModules env mod=do
    x<-aux env (S.singleton mod) M.empty
    let (ls,rs)=partitionEithers $ M.elems x
    if null ls
        then return $ return $ rs
        else return $ throwError $ concat ls


aux :: ModuleEnv
    -> S.Set String -- ^ modules to be parsed
    -> M.Map String (Either [CompileError] HsModule) -- ^ already parsed module
    -> IO (M.Map String (Either [CompileError] HsModule)) -- ^ all modules
aux env s m=case S.minView s of
    Nothing -> return m
    Just (s0,s') -> do x<-parseModule1 env s0
                       aux env (flip S.difference (M.keysSet m) $ S.union s' $ S.fromList $ either (const []) collectDep x) (M.insert s0 x m)



parseModule1 :: ModuleEnv -> String -> IO (Either [CompileError] HsModule)
parseModule1 env mod=do
    x<-modToPath env mod
    case x of
        Nothing -> return $ Left [CompileError "frontend" "" ("module "++mod++" not found\n")]
        Just ph -> do x<-readFile ph
                      case parseModuleWithMode (ParseMode ph) x of
                          ParseFailed loc msg -> return $ Left [CompileError "frontend" (show loc) msg]
                          ParseOk x           -> return $ Right x


collectDep :: HsModule -> [String]
collectDep (HsModule _ _ _ is _)="Prelude":map (uM . importModule) is
    where uM (Module x)=x

-- | convert module name to full file path.
modToPath :: ModuleEnv -> String -> IO (Maybe FilePath)
modToPath (ModuleEnv dirs) name=
    handle (\(SomeException _)->return Nothing) $ liftM Just $ firstM doesFileExist $ map (</>(name++".hs")) dirs

-- | Returns first element which satisfies the predicate.
firstM :: Monad m => (a -> m Bool) -> [a] -> m a
firstM f []=fail "firstM: not found"
firstM f (x:xs)=do
    e<-f x
    if e then return x else firstM f xs




-- | /strong/ desugar
-- Replaces all implicit pattern matching with explicit cases.
-- Explicit modification of SrcLoc for error reporting in later process.
sds :: HsModule -> Core
sds (HsModule _ _ _ _ decls)=Core (map convDataDecl ds) (map convFunDecl fs)
    where
        ds=filter isDataDecl decls
        fs=filter isFunBind decls






isDataDecl (HsDataDecl _ _ _ _ _ _)=True
isDataDecl _=False

isFunBind (HsFunBind _)=True
isFunBind _=False

isPatBind (HsPatBind _ _ _ _)=True
isPatBind _=False


convDataDecl :: HsDecl -> CrData
convDataDecl (HsDataDecl loc ctx (HsIdent name) vars cons derv)=
    CrData name [] $ map convDataCon cons

convDataCon :: HsConDecl -> (CrName,[(Bool,CrType)])
convDataCon (HsConDecl loc (HsIdent name) ts)=(name,map f ts)
    where f (HsBangedTy ty)=(True,convType ty)
          f (HsUnBangedTy ty)=(False,convType ty)

convFunDecl :: HsDecl -> CrProc
convFunDecl (HsFunBind [HsMatch loc (HsIdent n) args (HsUnGuardedRhs e) []])
    =CrProc n (map f args) (convExp e)
    where
        f (HsPVar (HsIdent x))=x
        f x=error $ show x


convDecl d=error $ "convDecl:ERROR:"++show d

convExp :: HsExp -> CrExpr
convExp (HsLambda loc as e)=CrLm (map f as) (convExp e)
    where
        f (HsPVar (HsIdent x))=x
convExp (HsVar (UnQual (HsIdent x)))=CrVar x
convExp (HsApp e0 e1)=CrApp (convExp e0) (convExp e1)
convExp e@(HsCase _ _)=convFullCase e
-- convExp (HsLit (HsInt n))=error "convExp: int"-- CrA (h,Nothing) $ CrInt $ fromIntegral n
convExp (HsLit (HsInt n))=CrByte $ fromIntegral n
convExp (HsLit (HsChar ch))=CrByte $ fromIntegral $ ord ch
convExp (HsLet bs e)=CrLet True (map (toVP . convFunDecl) bs) (convExp e)
    where
        toVP (CrProc v [] e)=(v,e)
        toVP (CrProc v as e)=(v,CrLm as e)
-- convExp h (HsExpTyeSig
convExp e=error $ "ERROR:convExp:"++show e


convType :: HsType -> CrType
convType (HsTyVar (HsIdent x))=CrTyVar x
convType (HsTyCon (UnQual (HsIdent x)))=CrTyCon x
convType (HsTyApp t0 t1)=CrTyApp (convType t0) (convType t1)
convType t=error $ "convType: "++show t


-- | Convert 'HsCase'(desugared) to 'CrExpr'
--
-- Sort 'HsAlt's by constructor and use 'procPartialCase' for each constructor.
--
-- One of the following:
--
-- * HsAlt (HsPApp ...
--
-- * HsAlt (HsPVar ...
convFullCase :: HsExp -> CrExpr
convFullCase (HsCase e as)=case md of
    Nothing    -> CrCase (convExp e) cs
    Just (v,f) -> CrLet False [(v,convExp e)] $ CrCase (CrVar v) $ ("",[],convExp f):cs
    where
        cs=mapMaybe cv $ M.assocs $ M.map (second $ map $ second $ convExp) mn
        
        (mn,md)=sortAlts as
        cv (cons,(arity,cs))=let vs=take arity $ stringSeq "#x"
                             in do{x<-convSeqCase (liftM (convExp . snd) md) (map CrVar vs) cs; return (cons,vs,x)}
            



-- | Transform case of multiple vars. Note that constructors are already removed by 'procFullCase'.
--
-- example:
--  
--  > case v1 v2 v3 of
--  >    p11 p12 p13 -> e1
--  >    p21 p22 p23 -> e2
--  >    _           -> fail
--
--  to
--
--  > case v1 v2 v3 of
--  >    p11 p12 p13 -> e1
--  >    _ -> case v1 v2 v3 of
--  >             p21 p22 p23 -> e2
--  >             _ -> fail
convSeqCase :: Maybe CrExpr -> [CrExpr] -> [([HsPat],CrExpr)] -> Maybe CrExpr
convSeqCase fail vs []=fail
convSeqCase fail vs ((ps,e):as)=return $ convAndCase (convSeqCase fail vs as) e (zip vs ps)

-- | Transform multiple vars to
-- 
-- >case v1 v2 v3 of
-- >    p1 u2 p3 -> succ
-- 
-- to
-- 
-- >case v1 of
-- >    p1 -> let u2=v2 in
-- >          case v3 of
-- >              p3 -> succ
-- >              _  -> fail(other 'HsAlt')
-- >    _ -> fail(other 'HsAlt')
--
convAndCase :: Maybe CrExpr -> CrExpr -> [(CrExpr,HsPat)] -> CrExpr
convAndCase fail succ []=succ
convAndCase fail succ ((v,pat):cs)=case pat of
    HsPVar (HsIdent p) ->
        CrLet False [(p,v)] next
    HsPApp (UnQual (HsIdent n)) args ->
        let das=take (length args) $ stringSeq "#x"
        in CrCase v $ maybe [] (\x->[("",[],x)]) fail++[(n,das,convAndCase fail next $ zip (map CrVar das) args)]
    where
        next=convAndCase fail succ cs


-- | Sort ['HsAlt'] by constructors.
sortAlts :: [HsAlt] -> (M.Map String (Int,[([HsPat],HsExp)]),Maybe (String,HsExp))
sortAlts []=(M.empty,Nothing)
sortAlts ((HsAlt loc pat (HsUnGuardedAlt e) []):as)=
    case pat of
        HsPApp (UnQual (HsIdent n)) args -> 
            (M.insertWith merge n (length args,[(args,e)]) mn,md)
        HsPVar (HsIdent v) -> (M.empty,Just (v,e))
        x -> error $ "sortAlts:"++show x
    where
        merge (n0,xs0) (n1,xs1)=if n0==n1 then (n0,xs0++xs1) else error $ "Unmatched arity@"++show loc
        (mn,md)=sortAlts as



showLoc :: SrcLoc -> LocHint
showLoc (SrcLoc file line col)=concat [file,":",show line,":",show col,":"]
-- convExp (HsCase e as)=CrCase 










-- | Merge 'HsModule's. TODO: implement qualification resolver.
mergeModules :: [HsModule] -> HsModule
mergeModules ms=HsModule (SrcLoc "<whole>" 0 0) (Module "<whole>") Nothing [] (concatMap f ms)
    where f (HsModule _ _ _ _ decls)=decls


-- | /medium/ desugaring
--
-- * introduces dummy variables
--
-- * 'HsPat' is handled manually(not via 'mds').
--
--  You might find that 'HsLambda','HsPatBind'->'HsCase' conversion here duplicates 'sds'.
-- But they're completely different because 'sds' considers evaluation sequence of 'HsAlt's.
class MidDesugar a where
    mds :: a -> a

instance MidDesugar HsModule where
    mds (HsModule loc mod exp imp ds)=HsModule loc mod exp imp (eliminatePBind $ map mds ds)

instance MidDesugar HsDecl where
    mds (HsFunBind ms)=mergeMatches $ map mds ms
    mds (HsPatBind loc pat (HsUnGuardedRhs e) decls)
        =HsPatBind loc pat (HsUnGuardedRhs $ mds $ moveDecls e decls) []
    mds d=d

instance MidDesugar HsExp where
    mds (HsCase e als)=HsCase (mds e) (map mds als)
    mds (HsLet decls e)=HsLet (eliminatePBind $ map mds decls) (mds e)
    mds (HsLambda loc ps e)=eliminatePLambda $ HsLambda loc ps (mds e)
    mds e=e

instance MidDesugar HsMatch where
    mds (HsMatch loc name ps (HsUnGuardedRhs e) decls)
        =HsMatch loc name ps (HsUnGuardedRhs $ mds $ moveDecls e decls) []

instance MidDesugar HsAlt where
    mds (HsAlt loc pat (HsUnGuardedAlt e) decls)
        =HsAlt loc pat (HsUnGuardedAlt $ mds $ moveDecls e decls) []


-- | Generate let with given decls and 'HsExp'
moveDecls :: HsExp -> [HsDecl] -> HsExp
moveDecls e []=e
moveDecls e ds=HsLet ds e


-- | Merge multiple 'HsMatch' in HsFunBind into one.
mergeMatches :: [HsMatch] -> HsDecl
mergeMatches []=error "Front: mergeMatches: empty [HsMatch] found!"
-- mergeMatches [m]=HsFunBind [m]
mergeMatches ms=HsFunBind [HsMatch loc0 n0 (map HsPVar args) (HsUnGuardedRhs expr) []]
    where
        HsMatch loc0 n0 ps0 _ _=head ms
        args=map (HsIdent . ("#a"++) . show) [0..length ps0-1]
        expr=HsCase (multiApp (stdTuple $ length args) $ map (HsVar . UnQual) args) $ map genAlt ms
        
        genAlt (HsMatch loc _ ps (HsUnGuardedRhs e) [])=HsAlt loc (wds $ HsPTuple ps) (HsUnGuardedAlt e) []

-- | Eliminate pattern matching in lambda arguments.
eliminatePLambda :: HsExp -> HsExp
eliminatePLambda (HsLambda loc ps e)=HsLambda loc (map fst vars) (f (map snd vars) e)
    where
        cat :: HsPat -> HsName -> (HsPat,Maybe (HsExp,HsPat))
        cat p@(HsPVar v) _=(p,Nothing)
        cat p r=(HsPVar r,Just (HsVar (UnQual r),p))
        
        vars=zipWith cat ps (map HsIdent $ stringSeq "#x")
        
        f :: [Maybe (HsExp,HsPat)] -> HsExp -> HsExp
        f [] e=e
        f (Nothing:vs) e=f vs e
        f ((Just (v,p)):vs) e=HsCase v [HsAlt loc p (HsUnGuardedAlt $ f vs e) []]


-- | Eliminate 'HsPatBind'
-- x:xs=f
-- ->
-- #t0=f
-- x=case #t0 of x:xs -> x
-- xs=case #t0 of x:xs -> x
--
eliminatePBind :: [HsDecl] -> [HsDecl]
eliminatePBind ds=concat $ zipWith (convertPBind True) (stringSeq "#x") $ map convSimple ds


-- | Convert obvious 'HsPatBind' to 'HsFunBind'
convSimple :: HsDecl -> HsDecl
convSimple (HsPatBind loc (HsPVar n) rhs [])=HsFunBind [HsMatch loc n [] rhs []]
convSimple d=d

-- | Convert 'HsPatBind' to ['HsFunBind'] recursively.
-- operation:
--
--   from: T x y=z
--
--   to: #=z; x=case # of T x y -> x; y=case # of T x y -> y
--
convertPBind :: Bool -> String -> HsDecl -> [HsDecl]
convertPBind _ _ (HsPatBind loc (HsPVar n) rhs [])=[HsFunBind [HsMatch loc n [] rhs []]]
convertPBind flag prefix (HsPatBind loc p0@(HsPApp n args) rhs [])
    |flag      = pre:concat (zipWith3 f vars p0s args)
    |otherwise = concat (zipWith3 f vars p0s args)
    where
        pre=HsFunBind [HsMatch loc (HsIdent prefix) [] rhs []]
        
        vars=map (((prefix++"_")++) . show) [0..]
        p0s=map (HsPApp n) $ change1 (map (HsPVar . HsIdent) vars) args
        
        f _ _ p@(HsPVar (HsIdent n))=[genDecl n p0]
        f v p0' p=genDecl v p0':convertPBind False v (HsPatBind loc p (HsUnGuardedRhs (stdVar v)) [])
        
        genDecl :: String -> HsPat -> HsDecl
        genDecl v p=HsFunBind [HsMatch loc (HsIdent v) [] (HsUnGuardedRhs e) []]
            where e=HsCase (stdVar prefix) [HsAlt loc p (HsUnGuardedAlt (stdVar v)) []]

convertPBind _ prefix x=[x]


-- | Literally convert 'HsPat' to 'HsExp'.
pat2con :: HsPat -> Maybe HsExp
pat2con (HsPVar n)=return $ HsVar (UnQual n)
pat2con (HsPApp n vs)=liftM (multiApp $ HsVar n) (mapM pat2con vs)
pat2con HsPWildCard=Nothing







-- | /weak/ desugaring
class WeakDesugar a where
    wds :: a -> a

instance WeakDesugar HsModule where
    wds (HsModule loc mod exp imp ds)=HsModule loc mod exp imp (map wds ds)

instance WeakDesugar HsDecl where
    wds (HsFunBind ms)=HsFunBind $ map wds ms
    wds (HsPatBind loc pat rhs decls)=HsPatBind loc (wds pat) (wds rhs) (map wds decls)
    wds (HsTypeSig loc ns ty)=HsTypeSig loc ns ty
    wds (HsDataDecl loc [] n vs cdecls [])=HsDataDecl loc [] n vs cdecls []
    wds (HsDataDecl _ _ _ _ _ _)=error "WeakDesugar: HsDataDecl: context/deriving is not supported"

instance WeakDesugar HsExp where
    wds (HsApp e0 e1)=HsApp (wds e0) (wds e1)
    wds (HsInfixApp e0 op e1)=HsApp (HsApp (wds $ opToExp op) (wds e0)) (wds e1)
    wds (HsNegApp e)=HsApp (HsVar (UnQual (HsIdent "negate"))) e
    wds (HsParen e)=wds e
    wds (HsLeftSection e op)=HsApp (opToExp op) (wds e)
    wds (HsRightSection op e)=HsApp (HsApp (HsVar (UnQual (HsIdent "flip"))) (opToExp op)) (wds e)
    wds (HsIf c e0 e1)=HsCase (wds c)
        [HsAlt wdsDummySrc (HsPApp (UnQual (HsIdent "True" )) []) (HsUnGuardedAlt (wds e0)) []
        ,HsAlt wdsDummySrc (HsPApp (UnQual (HsIdent "False")) []) (HsUnGuardedAlt (wds e1)) []]
    wds (HsCase e als)=HsCase (wds e) (map wds als)
    wds (HsLet decls e)=HsLet (map wds decls) (wds e)
    wds (HsLambda loc ps e)=HsLambda loc (map wds ps) (wds e)
    wds (HsEnumFrom e)=HsApp (stdVar "enumFrom") (wds e)
    wds (HsEnumFromTo e0 e1)=HsApp (HsApp (stdVar "enumFromTo") (wds e0)) (wds e1)
    wds (HsEnumFromThen e0 e1)=HsApp (HsApp (stdVar "enumFromThen") (wds e0)) (wds e1)
    wds (HsEnumFromThenTo e0 e1 e2)=HsApp (HsApp (HsApp (stdVar "enumFromThen") (wds e0)) (wds e1)) (wds e2)
    wds (HsCon f)=wds $ HsVar f
    wds (HsVar (Special HsCons))=stdVar "XCons"
    wds (HsVar (UnQual (HsSymbol v)))=HsVar (UnQual (HsIdent v))
    wds (HsVar v)=HsVar v
    wds (HsTuple es)=multiApp (stdTuple $ length es) (map wds es)
    wds (HsList es)=foldr (\x y->multiApp (stdVar "XCons") [wds x,y]) (stdVar "XNil") es
    wds (HsLit (HsString s))=wds $ HsList $ map (HsLit . HsChar) s
    wds l@(HsLit _)=l
    wds e=error $ "WeakDesugar:unsupported expression:"++show e

instance WeakDesugar HsMatch where
    wds (HsMatch loc name ps rhs decls)=HsMatch loc (wds name) (map wds ps) (wds rhs) (map wds decls)


instance WeakDesugar HsName where
    wds (HsSymbol x)=HsIdent x
    wds n=n

instance WeakDesugar HsQName where
    wds (Qual mod n)=Qual mod (wds n)
    wds (UnQual n)=UnQual (wds n)
    wds (Special sc)=UnQual $ HsIdent n
        where n=case sc of
                    HsUnitCon->"XT0"
                    HsListCon-> "XNil"
                    HsFunCon-> "XApp"
                    HsTupleCon n-> "XT"++show n
                    HsCons-> "XCons"

instance WeakDesugar HsPat where
    wds (HsPInfixApp p0 q p1)=HsPApp (wds q) [wds p0,wds p1]
    wds (HsPParen p)=wds p
    wds (HsPList ps)=foldr (\x y->HsPApp c [x,y]) n $ map wds ps
        where c=UnQual (HsIdent "XCons"); n=HsPApp (UnQual $ HsIdent "XNil") []
    wds (HsPTuple ps)=HsPApp (UnQual (HsIdent $ "XT"++show (length ps))) (map wds ps)
    wds (HsPApp n ps)=HsPApp (wds n) (map wds ps)
    wds (HsPVar n)=HsPVar $ wds n
    wds (HsPWildCard)=HsPWildCard
--    wds p=p
    wds p=error $ "WeakDesugar:unsupported HsPat:"++show p


instance WeakDesugar HsAlt where
    wds (HsAlt loc pat al decls)=HsAlt loc (wds pat) (wds al) (map wds decls)

-- | Only HsUnGuardedAlt will remain.
instance WeakDesugar HsGuardedAlts where
    wds (HsUnGuardedAlt e)=HsUnGuardedAlt $ wds e
    wds (HsGuardedAlts als)=HsUnGuardedAlt $ wds $ unguardG (\(HsGuardedAlt _ c e)->(c,e)) als

-- | Only HsUnGuardedRhs will remain.
instance WeakDesugar HsRhs where
    wds (HsUnGuardedRhs e)=HsUnGuardedRhs $ wds e
    wds (HsGuardedRhss rs)=HsUnGuardedRhs $ wds $ unguardG (\(HsGuardedRhs _ c e)->(c,e)) rs


-- | Generic unguarding routine (nested if generation)
unguardG :: (a -> (HsExp,HsExp)) -> [a] -> HsExp
unguardG _ []=HsVar $ UnQual $ HsIdent "undefined"
unguardG f (x:xs)=let (cond,exp)=f x in HsIf cond exp $ unguardG f xs

wdsDummySrc=SrcLoc "<WeakDesugar>" 0 0



stdVar :: String -> HsExp
stdVar=HsVar . UnQual . HsIdent

stdTuple :: Int -> HsExp
stdTuple=stdVar . ("XT"++) . show

opToExp :: HsQOp -> HsExp
opToExp (HsQVarOp n)=HsVar n
opToExp (HsQConOp n)=HsCon n

multiApp :: HsExp -> [HsExp] -> HsExp
multiApp=foldl HsApp



