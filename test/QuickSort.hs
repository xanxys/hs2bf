
main=outputStr Halt (qsort "etsb")

qsort []=[]
qsort (x:xs)=qsort (filter (gtByte x) xs)++[x]++qsort (filter (leByte x) xs)

outputStr k []=k
outputStr k (x:xs)=Output x (outputStr k xs)

