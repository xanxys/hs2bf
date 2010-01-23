-- fibonacci(complex)
main :: E
main=outputStr Halt $ concatMap cv fib

cv :: Integer -> List Char
cv n=showInteger n++"\n"

fib :: [Integer]
fib=1:1:zipWith (+) fib (tail fib)


