
import Control.Monad

import Language.Haskell.Parser
import Language.Haskell.Pretty
import Language.Haskell.Syntax


main=do
    let f="./test/Sample.hs"
    xs<-readFile f
    
    
    let px=parseModuleWithMode (ParseMode f) xs
    
    case px of
        ParseFailed loc msg -> putStrLn ("@"++show loc) >> putStrLn msg
        ParseOk c ->
            print c >> putStrLn "\n==========\n" >>
            putStrLn (prettyPrint (mds $ wds c)) >>putStrLn "\n==========\n" >>
            print (mds $ wds c)


-- | Core language - desugared Haskell
-- * a lot of useful transformations are done in this language
data Core v=Core [CrDecl v] deriving(Show)

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
    deriving(Show)


type CrName=String














-- | Desugaring policy: minimize the amount of code
-- 1. WeakDesugar
--   Shallow desugaring (including unguarding, if removal,)
-- 2. MidDesugar
--   A little bit deep desugaring (where -> let, pattern -> case, merge FunBinds)
--   introduces dummy variables
-- 3. StrDesugar
--   


-- | "medium" desugaring
class MidDesugar a where
    mds :: a -> a

instance MidDesugar HsModule where
    mds (HsModule loc mod exp imp ds)=HsModule loc mod exp imp (map mds ds)

instance MidDesugar HsDecl where
    mds (HsFunBind ms)=mergeMatches $ map mds ms
    mds (HsPatBind loc pat (HsUnGuardedRhs e) decls)
        =HsPatBind loc (mds pat) (HsUnGuardedRhs $ mds $ moveDecls e decls) []
    mds d=d

instance MidDesugar HsExp where
    mds (HsCase e als)=HsCase (mds e) (map mds als)
    mds (HsLet decls e)=HsLet (map mds decls) (mds e)
    mds (HsLambda loc ps e)=HsLambda loc (map mds ps) (mds e)
    mds e=e

instance MidDesugar HsMatch where
    mds (HsMatch loc name ps (HsUnGuardedRhs e) decls)
        =HsMatch loc name (map mds ps) (HsUnGuardedRhs $ mds $ moveDecls e decls) []

instance MidDesugar HsPat where
    mds (HsPParen p)=wds p
    mds p=p

instance MidDesugar HsAlt where
    mds (HsAlt loc pat (HsUnGuardedAlt e) decls)
        =HsAlt loc (mds pat) (HsUnGuardedAlt $ mds $ moveDecls e decls) []


moveDecls :: HsExp -> [HsDecl] -> HsExp
moveDecls e []=e
moveDecls e ds=HsLet ds e

mergeMatches :: [HsMatch] -> HsDecl
mergeMatches [m]=HsFunBind [m]
mergeMatches ms=HsFunBind [HsMatch loc0 n0 (map HsPVar args) (HsUnGuardedRhs expr) []]
    where
        HsMatch loc0 n0 ps0 _ _=head ms
        args=map (HsIdent . ("#a"++) . show) [0..length ps0-1]
        expr=HsCase (HsTuple $ map (HsVar . UnQual) args) $ map genAlt ms
        
        genAlt (HsMatch loc _ ps (HsUnGuardedRhs e) [])=HsAlt loc (HsPTuple ps) (HsUnGuardedAlt e) []
    

-- | "shallow" desugaring
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



opToExp :: HsQOp -> HsExp
opToExp (HsQVarOp n)=HsVar n
opToExp (HsQConOp n)=HsCon n

wdsDummySrc=SrcLoc "<WeakDesugar>" 0 0




