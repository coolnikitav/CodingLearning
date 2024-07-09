/**
 * Return an array of arrays of size *returnSize.
 * The sizes of the arrays are returned as *returnColumnSizes array.
 * Note: Both returned array and *columnSizes array must be malloced, assume caller calls free().
 */
int** construct2DArray(int* original, int originalSize, int m, int n, int* returnSize, int** returnColumnSizes) {
    int** two_d_array = (int**)malloc(m*sizeof(int*));

    if (m*n != originalSize) {
        *returnSize = 0;
        **returnColumnSizes = 0;
        return two_d_array;        
    }

    *returnSize = m;
    *returnColumnSizes = (int*)malloc(m*sizeof(int));

    for (int i = 0; i < m; i++) {
        int* row = (int*)malloc(n*sizeof(int));
        for (int j = 0; j < n; j++) {
            printf("i: %d, j: %d\n", i, j);

            row[j] = original[i*n + j];
        }
        two_d_array[i] = row;
        (*returnColumnSizes)[i] = n;
    }
    
    return two_d_array;
}
