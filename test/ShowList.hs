

main=outputStr Halt (map showByte1 [1,2,3,4])

showByte1 x=addByte '0' x

outputStr k []=k
outputStr k (x:xs)=Output x (outputStr k xs)

