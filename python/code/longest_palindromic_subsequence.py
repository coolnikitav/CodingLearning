def find_LPS(s, start_index, end_index):
  if start_index > end_index:
    return 0
  elif start_index == end_index:
    return 1
  elif s[start_index] == s[end_index]:
    return 2 + find_LPS(s, start_index+1, end_index-1)
  else:
    op1 = find_LPS(s, start_index, end_index-1)
    op2 = find_LPS(s, start_index+1, end_index)
    return max(op1, op2)

print(find_LPS("ELRMENMET", 0, 8))
