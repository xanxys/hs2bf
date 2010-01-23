
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
            putStrLn (prettyPrint (wds c)) >>putStrLn "\n==========\n" >>
            print (wds c)


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








-- | Convert decl-level pattern bindings to case
-- target: HsFunBind
-- cond: must be unguarded
unpatDecl :: HsDecl -> HsDecl
unpatDecl (HsPatBind loc pat rhs ds)=HsPatBind loc pat rhs ds
unpatDecl (HsFunBind ms)=HsFunBind [HsMatch loc0 n0 [HsPTuple $ map HsPVar args] (HsUnGuardedRhs expr) []]
    where
        HsMatch loc0 n0 ps0 _ _=head ms
        args=map (HsIdent . ("#arg"++) . show) [0..length ps0-1]
        expr=HsCase (HsTuple $ map (HsVar . UnQual) args) $ map genAlt ms
        
        genAlt (HsMatch loc _ ps (HsUnGuardedRhs e) decls)=HsAlt loc (HsPTuple ps) (HsUnGuardedAlt e) decls
        genAlt _=error "must unguard before unpatDecl"
unpatDecl d=d




-- | Core routine of unguarding (nested if generation)
unguardG :: (a -> (HsExp,HsExp)) -> [a] -> HsExp
unguardG _ []=HsVar $ UnQual $ HsIdent "undefined"
unguardG f (x:xs)=let (cond,exp)=f x in HsIf cond exp $ unguardG f xs






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
    mds (HsFunBind ms)=HsFunBind $ map wds ms
    mds (HsPatBind loc pat rhs decls)=HsPatBind loc (wds pat) (wds rhs) (map wds decls)
    mds d=d

instance MidDesugar HsExp where
    mds (HsCase e als)=HsCase (wds e) (map wds als)
    mds (HsLet decls e)=HsLet (map wds decls) e

instance MidDesugar HsMatch where
    mds (HsMatch loc name ps rhs decls)=HsMatch loc name (map mds ps) (mds rhs) (map mds decls)

instance MidDesugar HsPat where
    mds (HsPParen p)=wds p
    mds p=p

instance MidDesugar HsAlt where
    mds (HsAlt loc pat al decls)=HsAlt loc (mds pat) (mds al) (map mds decls)

instance MidDesugar HsGuardedAlts where
    mds (HsUnGuardedAlt e)=HsUnGuardedAlt $ mds e

instance MidDesugar HsRhs where
    mds (HsUnGuardedRhs e)=HsUnGuardedRhs $ mds e

    

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
    wds e=e

instance WeakDesugar HsMatch where
    wds (HsMatch loc name ps rhs decls)=HsMatch loc name (map wds ps) (wds rhs) (map wds decls)

instance WeakDesugar HsPat where
    wds (HsPParen p)=wds p
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




opToExp :: HsQOp -> HsExp
opToExp (HsQVarOp n)=HsVar n
opToExp (HsQConOp n)=HsCon n

wdsDummySrc=SrcLoc "<WeakDesugar>" 0 0




