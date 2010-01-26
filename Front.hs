-- | Haskell -> 'CoreP' desugarer
--
-- design policy: minimize the amount of code
--
-- [1. 'WeakDesugar' :: Hs -> Hs]
--   Shallow desugaring (including unguarding, if removal,)
--
-- [2. 'MidDesugar' :: Hs -> Hs]
--   A little bit deep desugaring (where -> let, pattern(PatBind,Lambda) -> case, merge FunBinds)
--   introduces dummy variables
--
-- [3. 'mergeModules' :: \[Hs\] -> Hs]
--   Resolve all name references and make them 'UnQual'.
--   Unknown identifiers are detected in this process.
--
-- [4. 'sds' :: Hs -> 'CoreP']
--   explicit pattern matching

module Front where
import Control.Monad
import Data.List
import Data.Maybe
import Language.Haskell.Parser
import Language.Haskell.Pretty
import Language.Haskell.Syntax

import Core



-- | Search all necesarry modules and parse them all (if possible).
-- If an parser error occurs, parse as many other files as possible to report further errors.
collectModules :: FilePath -> IO (Maybe [(FilePath,HsModule)])
collectModules path=do
    xs<-readFile path
    let px=parseModuleWithMode (ParseMode path) xs
    
    case px of
        ParseFailed loc msg -> putStrLn ("@"++show loc) >> putStrLn msg >> return Nothing
        ParseOk c->
--            print c >> putStrLn "\n==========\n" >>
            putStrLn (prettyPrint (mds $ wds c)) >> putStrLn "\n==========\n" >>
            print (mds $ wds c) >>
            return (Just [(path,c)])





{-

-- complex pattern decomposition HsExp:case
X (Y z w) y -> e
->
X #t0 y->case #t0 of Y zw -> e

-}


-- | /strong/ desugar
-- replace all implicit pattern matching with explicit cases.
sds :: HsModule -> CoreP
sds (HsModule _ _ _ _ decls)
    |null ps   = undefined
    |otherwise = undefined
    where
        ds=filter isDataDecl decls
        fs=filter isFunBind decls
        ps=filter isPatBind decls



isDataDecl (HsDataDecl _ _ _ _ _ _)=True
isDataDecl _=False

isFunBind (HsFunBind _)=True
isFunBind _=False

isPatBind (HsPatBind _ _ _ _)=True
isPatBind _=False













-- | Merge 'HsModule's.
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
mergeMatches [m]=HsFunBind [m]
mergeMatches ms=HsFunBind [HsMatch loc0 n0 (map HsPVar args) (HsUnGuardedRhs expr) []]
    where
        HsMatch loc0 n0 ps0 _ _=head ms
        args=map (HsIdent . ("#a"++) . show) [0..length ps0-1]
        expr=HsCase (HsTuple $ map (HsVar . UnQual) args) $ map genAlt ms
        
        genAlt (HsMatch loc _ ps (HsUnGuardedRhs e) [])=HsAlt loc (HsPTuple ps) (HsUnGuardedAlt e) []

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
eliminatePBind ds=concat $ zipWith convertPBind (stringSeq "#x") $ map convSimple ds


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
convertPBind :: String -> HsDecl -> [HsDecl]
convertPBind _ (HsPatBind loc (HsPVar n) rhs [])=[HsFunBind [HsMatch loc n [] rhs []]]
convertPBind prefix (HsPatBind loc p0@(HsPApp n args) rhs [])=pre:concat (zipWith f vars args)
    where
        pre=HsFunBind [HsMatch loc (HsIdent prefix) [] rhs []]
        
        vars=map (((prefix++"_")++) . show) [0..]
        
        f _ p@(HsPVar n)=maybeToList $ do e<-g p
                                          return $ HsFunBind [HsMatch loc n [] (HsUnGuardedRhs e) []]
        f vn p=case g p of
                   Nothing -> []
                   Just e -> convertPBind vn (HsPatBind loc p (HsUnGuardedRhs e) [])
        
        g :: HsPat -> Maybe HsExp
        g p=do e<-pat2con p
               return $ HsCase (HsVar (UnQual (HsIdent prefix))) [HsAlt loc p0 (HsUnGuardedAlt e) []]
convertPBind prefix x=[x]


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
    wds (HsInfixApp e0 op e1)=HsApp (HsApp (opToExp op) (wds e0)) (wds e1)
    wds (HsNegApp e)=HsApp (HsVar (UnQual (HsIdent "negate"))) e
    wds (HsParen e)=wds e
    wds (HsLeftSection e op)=HsApp (opToExp op) (wds e)
    wds (HsRightSection op e)=HsApp (HsApp (HsVar (UnQual (HsIdent "flip"))) (opToExp op)) (wds e)
    wds (HsIf c e0 e1)=HsCase (wds c)
        [HsAlt wdsDummySrc (HsPVar (HsIdent "True")) (HsUnGuardedAlt (wds e0)) []
        ,HsAlt wdsDummySrc (HsPVar (HsIdent "False")) (HsUnGuardedAlt (wds e1)) []]
    wds (HsCase e als)=HsCase (wds e) (map wds als)
    wds (HsLambda loc ps e)=HsLambda loc (map wds ps) (wds e)
    wds (HsEnumFrom e)=HsApp (stdVar "enumFrom") (wds e)
    wds (HsEnumFromTo e0 e1)=HsApp (HsApp (stdVar "enumFromTo") (wds e0)) (wds e1)
    wds (HsEnumFromThen e0 e1)=HsApp (HsApp (stdVar "enumFromThen") (wds e0)) (wds e1)
    wds (HsEnumFromThenTo e0 e1 e2)=HsApp (HsApp (HsApp (stdVar "enumFromThen") (wds e0)) (wds e1)) (wds e2)
    wds e=e

instance WeakDesugar HsMatch where
    wds (HsMatch loc name ps rhs decls)=HsMatch loc name (map wds ps) (wds rhs) (map wds decls)

instance WeakDesugar HsPat where
    wds (HsPInfixApp p0 q p1)=HsPApp q [wds p0,wds p1]
    wds (HsPParen p)=wds p
    wds (HsPList ps)=HsPList (map wds ps)
    wds (HsPTuple ps)=HsPTuple (map wds ps)
    wds (HsPApp n ps)=HsPApp n (map wds ps)
    wds p=p

instance WeakDesugar HsAlt where
    wds (HsAlt loc pat al decls)=HsAlt loc (wds pat) (wds al) (map wds decls)

-- | Only HsUnGuardedAlt remains.
instance WeakDesugar HsGuardedAlts where
    wds (HsUnGuardedAlt e)=HsUnGuardedAlt $ wds e
    wds (HsGuardedAlts als)=HsUnGuardedAlt $ wds $ unguardG (\(HsGuardedAlt _ c e)->(c,e)) als

-- | Only HsUnGuardedRhs remains.
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

opToExp :: HsQOp -> HsExp
opToExp (HsQVarOp n)=HsVar n
opToExp (HsQConOp n)=HsCon n

multiApp :: HsExp -> [HsExp] -> HsExp
multiApp=foldl HsApp

-- | a b c ... z aa ab ac ... az ba ...
-- avoid CAF.
stringSeq :: String -> [String]
stringSeq prefix=tail $ map ((prefix++) . reverse) $ iterate stringInc []

stringInc :: String -> String
stringInc []="a"
stringInc ('z':xs)='a':stringInc xs
stringInc (x:xs)=succ x:xs



