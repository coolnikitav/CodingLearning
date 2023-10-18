bool num_found(int* sums, int size, int num) {
    for (int i = 0; i < size; i++) {
        if (sums[i] == num) {
            return true;
        }
    }

    return false;
}

bool findSubarrays(int* nums, int numsSize){
    int* sums = (int* )malloc(numsSize * sizeof(int));

    for (int i = 0; i < numsSize-1; i++) {
        int sum = nums[i] + nums[i+1];

        if (num_found(sums, numsSize, sum)) {
            free(sums);
            return true;
        }
        else {
            sums[i] = sum;
        }
    }
    free(sums);
    return false;
}
