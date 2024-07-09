# This solution can be optimized by using a map
class Solution(object):
    def incrementRow(self, matrix, row_index):
        for col_index in range(len(matrix[0])):
            matrix[row_index][col_index] += 1

    def incrementCol(self, matrix, col_index):
        for row_index in range(len(matrix)):
            matrix[row_index][col_index] += 1

    def oddCells(self, m, n, indices):
        """
        :type m: int
        :type n: int
        :type indices: List[List[int]]
        :rtype: int
        """
        matrix = [[0]*n for i in range(m)]
        for i in range(0, len(indices)):
            self.incrementRow(matrix, indices[i][0])
            self.incrementCol(matrix, indices[i][1])

        odd_cells = 0

        for i in range(len(matrix)):
            for j in range(0, len(matrix[0])):
                if matrix[i][j] % 2 == 1:
                    odd_cells += 1

        return odd_cells
