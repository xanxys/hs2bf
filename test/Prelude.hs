
data Bool
    =True
    |False

data XT2 a b=XT2 a b

data XList a
    =XCons a (XList a)
    |XNil

data E
    =Input (Char -> E)
    |Output Char E
    |Halt


