
infixr 0 $
f $ x=f x

f $! x=x `seq` (f x)

data Bool
    =False
    |True

data Ordering
    =EQ -- 0
    |LT -- 1
    |GT -- 2

data XT1 a=XT1 a
data XT2 a b=XT2 a b
data XT3 a b c=XT3 a b c

data XList a
    =XCons a (XList a)
    |XNil

data E
    =Input (Char -> E)
    |Output !Char E
    |Halt

otherwise=True

--seq x y=y
seq=undefined
undefined=undefined


addByteRaw=undefined
subByteRaw=undefined
cmpByteRaw=undefined

addByte x y=x `seq` (y `seq` (addByteRaw x y))
subByte x y=x `seq` (y `seq` (subByteRaw x y))
cmpByte x y=x `seq` (y `seq` (cmpByteRaw x y))

eqByte x y=case cmpByte x y of
    EQ -> True
    s  -> False

ltByte x y=case cmpByte x y of
    LT -> True
    s  -> False

gtByte x y=case cmpByte x y of
    GT -> True
    s  -> False

leByte x y=case cmpByte x y of
    GT -> False
    s  -> True

geByte x y=case cmpByte x y of
    LT -> False
    s  -> True

{-
data Int
    =PInt Byte
    |NInt Byte


negateInt (PInt x)=NInt x
negateInt (NInt x)=PInt x

addInt (PInt x) (PInt y)=PInt $ x `addByte` y
addInt (NInt x) (NInt y)=NInt $ x `addByte` y
addInt (PInt x) (NInt y)
    |x `gtByte` y = PInt $ x `subByte` y
    |otherwise    = NInt $ y `subByte` x
addInt (NInt x) (PInt y)
    |x `gtByte` y = NInt $ x `subByte` y
    |otherwise    = PInt $ y `subByte` x

-}


-- list functions
head (x:xs)=x
tail (x:xs)=xs

reverse []=[]
reverse (x:xs)=reverse xs++[x]

map f []=[]
map f (x:xs)=f x:map f xs

filter f []=[]
filter f (x:xs)
    |f x       = x:filter f xs
    |otherwise = filter f xs

(x:xs) !! n
    |n `eqByte` 0 = x
    |otherwise    = xs !! (n `subByte` 1)

{- I don't know why, but this code doesn't work!
[]++ys=ys
(x:xs)++ys=x:(xs++ys)
-}

xs ++ ys=
    case xs of
        []   -> ys
        x:xs -> x:(xs++ys)
    

length []=0
length (x:xs)=1 `addByte` (length xs)

foldr f z []=z
foldr f z (x:xs)=f x (foldr f z xs)

foldl f z []=z
foldl f z (x:xs)=foldl f (f x z) xs

