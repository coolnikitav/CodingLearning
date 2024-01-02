from collections import deque,defaultdict

class Solution(object):
    def nearestExit(self, maze, entrance):
        """
        :type maze: List[List[str]]
        :type entrance: List[int]
        :rtype: int
        """
        maze_length = len(maze)
        maze_width = len(maze[0])

        # Create an adjacency list of cell and a list of its neighbors
        adj_list = defaultdict(list)

        for row_idx in range(maze_length):
            for col_idx in range(maze_width):
                if maze[row_idx][col_idx] == ".":                         
                    adj_list[(row_idx,col_idx)] = []
                    if row_idx > 0:
                        if maze[row_idx-1][col_idx] == ".":
                            adj_list[(row_idx,col_idx)].append((row_idx-1,col_idx))
                    if row_idx < len(maze)-1:
                        if maze[row_idx+1][col_idx] == ".":
                            adj_list[(row_idx,col_idx)].append((row_idx+1,col_idx))
                    if col_idx > 0:
                        if maze[row_idx][col_idx-1] == ".":
                            adj_list[(row_idx,col_idx)].append((row_idx,col_idx-1))
                    if col_idx < len(maze[0])-1:
                        if maze[row_idx][col_idx+1] == ".":
                            adj_list[(row_idx,col_idx)].append((row_idx,col_idx+1))
        
        def print_dict(dictionary):
            for key in dictionary:
                print("("+str(key[0])+","+str(key[1])+") : ",end="")
                for value in dictionary[key]:
                    print("("+str(value[0])+","+str(value[1])+") ",end="")
                print("")

        print_dict(adj_list)
        
        # Do BFS on the list and record lengths as you reach exits
        def bfs(entrance):
            path_list = []

            visited_cells = set()
            visited_cells.add((entrance[0],entrance[1]))

            cell_queue = deque([(entrance[0],entrance[1],0)])

            while cell_queue:
                current_cell = cell_queue.popleft()
                row_idx = current_cell[0]
                col_idx = current_cell[1]

                if (row_idx == 0 or row_idx == maze_length-1 or col_idx == 0 or col_idx == maze_width-1) and ((row_idx,col_idx) != (entrance[0],entrance[1])):
                    return current_cell[2]
                
                for neighbor_cell in adj_list[(current_cell[0],current_cell[1])]:
                    if (neighbor_cell[0],neighbor_cell[1]) not in visited_cells:
                        visited_cells.add((neighbor_cell[0],neighbor_cell[1]))
                        cell_queue.append((neighbor_cell[0],neighbor_cell[1],current_cell[2]+1))
            return -1


        # Return the shortest length
        return bfs(entrance)
        
            
test = Solution()
maze = [["+","+",".","+"],[".",".",".","+"],["+","+","+","."]] 
entrance = [1,2]
print(test.nearestExit(maze,entrance))
