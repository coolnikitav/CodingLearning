def findRotatedIndex(arr, num):
    l = 0
    r = len(arr)-1
    
    # List is empty
    if len(arr) == 0:
        return -1
        
    while l <= r:
        m = (l+r)//2
        
        if num == arr[m]:
            return m
            
        # Left half is sorted
        if arr[m] > arr[l]:
            if num < arr[m] and num >= arr[l]:
                r = m-1
            else:
                l = m+1
        
        # Right half is sorted
        else:
            if num > arr[m] and num <= arr[r]:
                l = m+1
            else:
                r = m-1
    return -1

print(findRotatedIndex([3, 4, 1, 2], 4)) # 1
print(findRotatedIndex([4, 6, 7, 8, 9, 1, 2, 3, 4], 8)) # 3
print(findRotatedIndex([6, 7, 8, 9, 1, 2, 3, 4], 3)) # 6
print(findRotatedIndex([37, 44, 66, 102, 10, 22], 14)) # -1
print(findRotatedIndex([6, 7, 8, 9, 1, 2, 3, 4], 12)) # -1
print(findRotatedIndex([11, 12, 13, 14, 15, 16, 3, 5, 7, 9], 16)) # 5
print(findRotatedIndex([11, 12, 13, 17, 39], 17)) # 3
print(findRotatedIndex([11], 11)) # 0
print(findRotatedIndex([], 11)) # -1
print(findRotatedIndex([4, 4, 4, 4, 4], 5)) # -1