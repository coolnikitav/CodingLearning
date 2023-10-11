def pivot(arr, comparator=None, start=0):
    if callable(comparator == False):
        def comparator(a,b):
            if a > b:
                return 1
            elif a < b:
                return -1
            else:
                return 0
        
    pivot = start
    swap = start
    for i in range(start+1, len(arr)):
        if arr[i] < arr[pivot]:
            swap += 1
            [arr[swap], arr[i]] = [arr[i], arr[swap]]
    if pivot != start:
        [arr[pivot], arr[start]] = [arr[start], arr[pivot]]
    return pivot

def quickSort(arr, comparator=None, start = 0, end=0):
    if start < end:
        pivot_index = pivot(arr, comparator, start)
        quickSort(arr, start, pivot_index-1)
        quickSort(arr, pivot_index+1, end)
    return arr
    