def countZeroes(customList):
    length = len(customList)
    l = 0
    r = length - 1
    m = (l+r)//2
    
    while l <= r:
        if customList[m] == 1:
            l = m+1
        else:
            r = m-1
        m = (l+r)//2
    return length - m - 1

print(countZeroes([1,1,1,1,0,0])) # 2
print(countZeroes([1,0,0,0,0])) # 4
print(countZeroes([0,0,0])) # 3
print(countZeroes([1,1,1,1])) # 0