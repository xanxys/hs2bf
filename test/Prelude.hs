
data Bool
    =True
    |False

data XList a
    =XCons a (XList a)
    |XNil

data E
    =Input (Char -> E)
    |Output Char E
    |Halt


