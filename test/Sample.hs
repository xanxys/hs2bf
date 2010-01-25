
-- this is not indented to be a complete haskell compiler!
-- no GADT
-- no class/instance
-- no bang-patterns
-- no enums
-- data types: Cell(8bit)





main :: E
main=Halt

test []=1
    where y=2

test (x:xs)=2
    where
        z x=3
        z y=4

xyz2 x|x==1 = 2
      |otherwise =3

f x y=x+y


-- TODO: (very rarely used)
-- numbers=[0..]
-- x:xs=numbers


-- internal library
data Bool=False|True
data Char=Char Byte
data Integer=Integer [Byte]

(Integer (x:xs))+(Integer (y:ys))
    |lt z x || lt z y = z:(xs+ys+Integer [1])
    |otherwise = z:(xs+ys)
    where z=x+y
(Integer [])+xs=xs
xs+(Integer [])=xs




x:xs=[1..]
    
{-
enumFrom :: a -> [a]	Source
Used in Haskell's translation of [n..].
enumFromThen :: a -> a -> [a]	Source
Used in Haskell's translation of [n,n'..].
enumFromTo :: a -> a -> [a]	Source
Used in Haskell's translation of [n..m].
enumFromThenTo :: a -> a -> a -> [a]
-}

-- primitives:
--  Byte
--  lt,gt,add,sub
xyz=undefined
    where
        x x=[0..1]
        x y=[0..1]
mergeMatches :: [HsMatch] -> HsDecl
mergeMatches [m]=HsFunBind [m]
mergeMatches ms=HsFunBind [HsMatch loc0 n0 (map HsPVar args) (HsUnGuardedRhs expr) []]
    where
        HsMatch loc0 n0 ps0 _ _=head ms
        args=map (HsIdent . ("#a"++) . show) [0..length ps0-1]
        expr=HsCase (HsTuple $ map (HsVar . UnQual) args) $ map genAlt ms
        
        genAlt (HsMatch loc _ ps (HsUnGuardedRhs e) [])=HsAlt loc (HsPTuple ps) (HsUnGuardedAlt e) []
    
