int sumOfSquares(int* nums, int numsSize){
    int sum_of_squares = 0;

    for (int i = 0; i < numsSize; i++) {
        if (numsSize % (i+1) == 0) {
            sum_of_squares += nums[i] * nums[i];
        }
    }

    return sum_of_squares;
}
