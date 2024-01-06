def longestCommonSubsequence(text1, text2):
    text1_len = len(text1)
    text2_len = len(text2)

    grid = [[0 for _ in range(text2_len+1)] for _ in range(text1_len+1)]

    for row in range(text1_len-1,-1,-1):
        for col in range(text2_len-1,-1,-1):
            if text1[row] == text2[col]:
                grid[row][col] = 1 + grid[row+1][col+1]
            else:
                grid[row][col] = max(grid[row+1][col],grid[row][col+1])
    
    return grid[0][0]

print(longestCommonSubsequence("abcde","ace"))