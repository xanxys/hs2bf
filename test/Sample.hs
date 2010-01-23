
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


-- primitives:
--  Byte
--  lt,gt,add,sub

