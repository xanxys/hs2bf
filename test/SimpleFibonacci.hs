-- fibonacci(simple)
main :: E
main=outputStr Halt $ concatMap cv fib

outputStr k []=k
outputStr k (x:xs)=Output x $ outputStr k xs

cv :: Integer -> [Char]
cv n=if n==0 then "\n" else '*':cv (n-1)

fib :: [Integer]
fib=1:1:zipWith (+) fib (tail fib)

