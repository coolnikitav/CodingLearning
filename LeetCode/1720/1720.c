/**
 * Note: The returned array must be malloced, assume caller calls free().
 */
int* decode(int* encoded, int encodedSize, int first, int* returnSize){
    *returnSize = encodedSize+1;
    int* return_array = (int*)malloc(*returnSize * sizeof(int));

    return_array[0] = first;

    for (int i = 0; i < encodedSize; i++) {
        int return_num = return_array[i]^encoded[i];
        return_array[i+1] = return_num;
    }

    return return_array;
}
