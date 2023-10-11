def sortedFrequency(arr, num):
    arr_length = len(arr)
    left = 0
    right = arr_length-1
    
    if arr_length == 0:
        return -1

    while arr[left] != num or arr[right] != num:
        if left > right:
            return -1
        
    return right-left

print(sortedFrequency([1, 1, 2, 2, 2, 2, 3], 2)) # 4
print(sortedFrequency([1, 1, 2, 2, 2, 2, 3], 3)) # 1
print(sortedFrequency([1, 1, 2, 2, 2, 2, 3], 4)) # -1
print(sortedFrequency([], 4)) # -1