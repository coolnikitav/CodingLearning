#include<stdio.h>
#include<stdbool.h>

int alternateDigitSum(int n) {
    int num_digits = 0;
    int sum = 0;
    bool odd = true;

    while (n > 0) {
        if (odd) {
            sum += n%10;
            odd = false;
        } else {
            sum -= n%10;
            odd = true;
        }
        
        n /= 10;
        num_digits++;
    }

    if (num_digits%2 == 0) {
        sum *= -1;
    }
    
    return sum;
}

int main() {
    int n1 = 123;
    printf("Test 1: n = 123\nExpected: 2 \nActual: %d\n", alternateDigitSum(n1));

    int n2 = 1234;
    printf("Test 2: n = 1234\nExpected: -2 \nActual: %d\n", alternateDigitSum(n2));

    int n3 = 5;
    printf("Test 4: n = 5\nExpected: 5 \nActual: %d\n", alternateDigitSum(n3));

    return 0;
}
