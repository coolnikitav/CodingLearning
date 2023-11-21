#include<stdio.h>

int hammingDistance(int x, int y) {
    int hamming_num = x ^ y;
    int diff = 0;

    while (hamming_num > 0) {
        if (hamming_num % 2 == 1) {
            diff++;
        }
        hamming_num /= 2;
    }

    return diff;
}

int main() {
    printf("%d\n", hammingDistance(1,4));
    printf("%d\n", hammingDistance(3,1));
    return 0;
}
