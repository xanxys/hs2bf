
main=outputStr Halt "Hello World!"
--main=outputStr Halt "He"

outputStr k []=k
outputStr k (x:xs)=Output x (outputStr k xs)

