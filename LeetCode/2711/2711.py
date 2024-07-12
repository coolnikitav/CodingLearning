class Solution:
    def differenceOfDistinctValues(self, grid: List[List[int]]) -> List[List[int]]:
        diff = [[0] * len(grid[0]) for _ in range(len(grid))]
        for i in range(len(grid)):
            for j in range(len(grid[0])):
                left = set()
                right = set()
                n = 1
                while i-n >=0 and j-n >= 0:
                    left.add(grid[i-n][j-n])
                    n += 1
                n = 1
                while i+n < len(grid) and j+n < len(grid[0]):
                    right.add(grid[i+n][j+n])
                    n += 1
                diff[i][j] = abs(len(left) - len(right))
        return diff
