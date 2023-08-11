class Solution(object):
    def equalPairs(self, grid):
        """
        :type grid: List[List[int]]
        :rtype: int
        """

        count = 0

        rows = dict()
        columns = dict()

        # Add rows and their frequencies to the rows map
        for row in grid:
            row = tuple(row)
            if row not in rows:
                rows[row] = 1
            else:
                rows[row] += 1
        
        # Transpose the matrix
        grid = [ [ grid[j][i] for j in range(len(grid)) ] for i in range(len(grid[0])) ]

        # Add columns and their frequencies to the columns map
        for column in grid:
            column = tuple(column)
            if column not in columns:
                columns[column] = 1
            else:
                columns[column] += 1

        # Update the pair count
        for row in rows:
            if row in columns:
                count += rows[row] * columns[row]  # 2 rows and 1 column would give us 2 pairs

        return count
