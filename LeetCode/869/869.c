#include<stdio.h>
#include<stdbool.h>

bool isMonotonic(int* nums, int numsSize) {
    if (numsSize == 1) {
        return true;
    }

    bool increasing = true, decreasing = true;

    for (int i = 0; i < numsSize-1; i++) {
        if (nums[i+1] > nums[i]) {
            decreasing = false;
        } else if (nums[i+1] < nums[i]) {
            increasing = false;
        }

        if (!increasing && !decreasing) {
            return false;
        }
    }

    return true;
}

int main() {
    int nums1[4] = {1,2,2,3};
    printf("Results of test 1 : [1,2,2,3] is %d. Expected: 1\n", isMonotonic(nums1, 4));
    
    int nums2[4] = {6,5,4,4};
    printf("Results of test 2 : [6,5,4,4] is %d. Expected: 1\n", isMonotonic(nums2, 4));

    int nums3[3] = {1,3,2};
    printf("Results of test 3 : [1,3,2] is %d.   Expected: 0\n", isMonotonic(nums3, 3));

    int nums4[1] = {1};
    printf("Results of test 4 : [1] is %d.       Expected: 1\n", isMonotonic(nums4, 1));

    int nums5[3] = {1,1,1};
    printf("Results of test 5 : [1,1,1] is %d.   Expected: 1\n", isMonotonic(nums5, 0));

    int nums6[4] = {1,1,2,3};
    printf("Results of test 6 : [1,1,2,3] is %d. Expected: 1\n", isMonotonic(nums6, 4));

    return 0;
}
