def find_min_operation(s1, s2, index1, index2):
  if index1 == len(s1):
    return len(s2) - index2
  if index2 == len(s2):
    return len(s1) - index1
  if s1[index1] == s2[index2]:
    return find_min_operation(s1, s2, index1+1, index2+1)
  else:
    delete_op = 1 + find_min_operation(s1, s2, index1, index2+1)
    insert_op = 1 + find_min_operation(s1, s2, index1+1, index2)
    replace_op = 1 + find_min_operation(s1, s2, index1+1, index2+1)
    return min(delete_op, insert_op, replace_op)

print(find_min_operation("table", "tbrles", 0, 0))
