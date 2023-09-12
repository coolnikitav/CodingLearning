def find_min_cost(twoD_array, row, col):
  if row == -1 and col == -1:
    return float('inf')
  elif row == 0 and col == 0:
    return twoD_array[0][0]
  else:
    op1 = find_min_cost(twoD_array, row-1, col)
    op2 = find_min_cost(twoD_array, row, col-1)
    return twoD_array[row][col] + min(op1, op2)

TwoDList = [[4,7,8,6,4],
           [6,7,3,9,2],
           [3,8,1,2,4],
           [7,1,7,3,7],
           [2,9,8,9,3]
           ]

print(findMinCost(TwoDList, 4,4))
