-- fibonacci(complex)
main :: E
main=outputStr Halt $ concatMap cv fib

cv :: Integer -> List Char
cv n=showInteger n++"\n"

fib :: [Integer]
fib=1:1:zipWith (+) fib (tail fib)

concatMap=concat . map

map f []=[]
map f (x:xs)=f x:map f xs

concat []=[]
concat (xs:xss)=xs++concat xss

[] ++ ys=ys
(x:xs) ++ ys=x:(xs++ys)

zipWith f (x:xs) (y:ys)=f x y:zipWith xs ys
zipWith _ _ _=[]

head (x:xs)=x
tail (x:xs)=xs

-- only support non-negative integer.
showInteger :: Integer -> String
showInteger n
    |n<10      = showDigit n
    |otherwise = let (d,m)=divmod n 10 in showDigit m:showInteger d

showDigit=chr . (+ord '0')
                     
