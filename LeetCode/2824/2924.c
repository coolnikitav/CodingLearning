#include<stdio.h>

int countPairs(int* nums, int numsSize, int target){
    int pairs = 0;

    for (int i = 0; i < numsSize-1; i++) {
        for (int j = i+1; j < numsSize; j++) {
            if (nums[i] + nums[j] < target) {
                pairs++;
            }
        }
    }

    return pairs;
}

int main() {
    int num1[5] = {-1,1,2,3,1};
    printf("%d\n", countPairs(num1, 5, 2));

    int num2[7]= {-6,2,5,-2,-7,-1,3};
    printf("%d\n", countPairs(num2, 7, -2));

    return 0;
}
