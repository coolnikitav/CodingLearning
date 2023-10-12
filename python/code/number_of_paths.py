def number_of_paths(twoD_array, row, col, cost):
  if cost < 0:
    return 0
  elif row == 0 and col == 0:
    if twoD_array[0][0] - cost == 0:
      return 1
    else:
      return 0
  elif row == 0:
    return number_of_paths(twoD_array, 0, col-1, cost - twoD_array[row][col])
  elif col == 0:
    return number_of_paths(twoD_array, row-1, 0, cost - twoD_array[row][col])
  else:
    op1 = number_of_paths(twoD_array, row-1, col, cost - twoD_array[row][col])
    op2 = number_of_paths(twoD_array, row, col-1, cost - twoD_array[row][col])
    return op1 + op2

TwoDList = [[4,7,1,6],
           [5,7,3,9],
           [3,2,1,2],
           [7,1,6,3]
           ]

print(numberOfPaths(TwoDList, 3,3, 25))
