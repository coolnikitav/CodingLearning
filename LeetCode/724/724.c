int pivotIndex(int* nums, int numsSize) {
    int total_sum = 0;

    for (int i = 0; i < numsSize; i++) {
        total_sum += nums[i];
    }

    int left_sum = 0;

    for (int i = 0; i < numsSize; i++) {
        if (left_sum == (total_sum - nums[i] - left_sum)) {
            return i;
        }
        left_sum += nums[i];
    }

    return -1;
}
