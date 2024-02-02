#include <stdlib.h>
#include <stdio.h>

int* sequentialDigits(int low, int high, int* returnSize) {
    int seq_nums[36] = {12, 23, 34, 45, 56, 67, 78, 89, 123, 234, 345, 456, 567, 678, 789, 1234, 2345, 3456, 4567, 5678, 6789, 12345, 23456, 34567, 45678, 56789, 123456, 234567, 345678, 456789, 1234567, 2345678, 3456789, 12345678, 23456789, 123456789};
    int beg=0,end=0;
    for (int i = 0; i < 36; i++) {
        if (seq_nums[i] < low) {
            beg++;
        }
        if (seq_nums[i] <= high) {
            end++;
        }
    }

    *returnSize = end-beg;
    int* return_arr = (int*)malloc(*returnSize * sizeof(int));

    for (int i = 0; i < *returnSize; i++) {
        return_arr[i] = seq_nums[beg+i];
    }
    return return_arr;
}

void print_arr(int* arr) {
    int arr_size = sizeof(arr)/sizeof(arr[0]);
    printf("[");
    for (int i = 0; i < arr_size; i++) {
        printf("%d, ", arr[i]);
    }
    printf("]\n");
}

int main() {
    int returnSize1;
    print_arr(sequentialDigits(100,300,&returnSize1));

    int returnSize2;
    print_arr(sequentialDigits(1000,13000,&returnSize2));
}
