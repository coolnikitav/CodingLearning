def rotate(matrix):
    return (mirror(transpose(matrix)))
    
def transpose(matrix):
    for i in range(len(matrix)):
        for j in range(i+1, len(matrix)):
            matrix[i][j],matrix[j][i] = matrix[j][i],matrix[i][j]
    return matrix
    
def mirror(matrix):
    for i in range(len(matrix)):
        for j in range(len(matrix)//2):
            matrix[i][j],matrix[i][len(matrix)-1-j] = matrix[i][len(matrix)-1-j],matrix[i][j]
    return matrix

matrix1 = [[1,2,3],[4,5,6],[7,8,9]]

matrix2 = [[1,2,3,4],[5,6,7,8],[9,10,11,12],[13,14,15,16]]

print(matrix1)
matrix1 = transpose(matrix1)
print(matrix1)
matrix1 = mirror(matrix1)
print(matrix1)

print(matrix2)
matrix2 = transpose(matrix2)
print(matrix2)
matrix2 = mirror(matrix2)
print(matrix2)