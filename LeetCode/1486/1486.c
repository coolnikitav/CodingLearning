#include<stdio.h>

int xorOperation(int n, int start) {
    int result = start;
    for (int i = 0; i < n; i++) {
        start += 2;
        result ^= start;
    }

    return result;
}

int main() {
    printf("%d\n", xorOperation(5, 0));

    printf("%d\n", xorOperation(4, 3));
    return 0;
}
