/**
 * Note: The returned array must be malloced, assume caller calls free().
 */
int num_of_digits(int num) {
    int num_of_digits = 0;
    while (num > 0) {
        num_of_digits++;
        num /= 10;
    }

    return num_of_digits;
}

void append_digits(int* digits, int* digits_index, int num) {
    while (num > 0) {
        digits[*digits_index] = num%10;
        num /= 10;
        (*digits_index)--;
    }
}

int* separateDigits(int* nums, int numsSize, int* returnSize) {
    int total_digits = 0;

    for (int i = 0; i < numsSize; i++) {
        total_digits += num_of_digits(nums[i]);
    }

    int* digits = (int*)malloc(total_digits * sizeof(int));
    int digits_index = total_digits-1;

    for (int i = numsSize-1; i >= 0; i--) {
        append_digits(digits, &digits_index, nums[i]);
    }
    *returnSize = total_digits;
    return digits;
}
