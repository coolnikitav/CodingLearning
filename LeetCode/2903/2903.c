int* findIndices(int* nums, int numsSize, int indexDifference, int valueDifference, int* returnSize) {
    *returnSize = 2;
    int* returnArray = (int*)malloc(*returnSize * sizeof(int));  

    for (int i = 0; i + indexDifference < numsSize; i++) {
        for (int j = i + indexDifference; j < numsSize; j++) {
            if (abs(nums[i] - nums[j]) >= valueDifference) {
                returnArray[0] = i;
                returnArray[1] = j;
                return returnArray;
            }
        }
    }
    returnArray[0] = -1;
    returnArray[1] = -1;
    return returnArray;
}
