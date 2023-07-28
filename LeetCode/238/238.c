/**
 * Note: The returned array must be malloced, assume caller calls free().
 */
int* productExceptSelf(int* nums, int numsSize, int* returnSize){
    int *output = malloc(sizeof(int) * numsSize);
    int pre = 1;
    int suf = 1;
    
    for (int i = 0; i < numsSize; i++) {
        output[i] = 1;
    }

    for (int i = 0; i < numsSize; i++) {
        output[i] *= pre;
        pre *= nums[i];
        output[numsSize-1-i] *= suf;
        suf *= nums[numsSize-1-i];
    }

    *returnSize = numsSize;
    return output;
}
