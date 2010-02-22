
main=outputStr Halt "Hello!"

outputStr k []=k
outputStr k (x:xs)=Output x (outputStr k xs)

