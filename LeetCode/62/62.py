class Solution:
    def uniquePaths(self, m, n): 
        grid = [[0 for _ in range(n+m-1)] for _ in range(m)]
        for row in range(m):
            grid[row][0] = 1
        for col in range(n+m-1):
            grid[0][col] = 1

        for col in range(2,n+m-1):
             temp_col = col-1
             row = 1
             while temp_col >= 1 and row < m:
                 up_cell = grid[row-1][temp_col]
                 left_cell = grid[row][temp_col-1]
                 grid[row][temp_col] = up_cell + left_cell
                 
                 row += 1
                 temp_col -= 1

        return grid[m-1][n-1]

test = Solution()
print(test.uniquePaths(3,7))