class NQueens:
  def __init__(self, n):
    self.n = n
    self.chess_table = [[0 for i in range(n)] for j in range(n)]

  def print_queens(self):
    for i in range(self.n):
      for j in range(self.n):
        if self.chess_table[i, j] == 1:
          print(" Q ", end = '')
        else:
          print(" - ", end='')
      print("\n")

  def is_place_safe(self, row_index, col_index):
    

queens = NQueens(4)
queens.print_queens()
