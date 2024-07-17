#include <stdio.h>
#include <stdlib.h>

int max_fn(int a, int b) {
    return a > b ? a : b;
}

char* addBinary(char* a, char* b) {
    // Determine the size of the output. If MSB of a or b are both 1, output will be max(len of a, len of b) + 1, else max(len of a, len of b)
    printf("%s, %s\n", a, b);
    int len_a = sizeof(a);
    int len_b = sizeof(b);
    int len_add = (a[0] == '1' && b[0] == '1') ? (max_fn(len_a, len_b) + 1) : max_fn(len_a, len_b);
    printf("len_a: %d, len_b: %d, len_add: %d", len_a, len_b, len_add);

    char* add = (char*)malloc(len_add);

    int carry = 0;
    int i;
    int j;
    for (i = len_a, j = len_b; i >= 0 && j >= 0; i--, j--) {
        if (carry) {
            if (a[i] == '1' && b[j] == '1') {
                add[i] = '1';
            } else if (add[i] == '0' && b[j] == '0') {
                add[i] = '1';
                carry = 0;
            } else {
                add[i] = '0';
                carry = 0;
            }
        } else {
            if (a[i] == '1' && b[j] == '1') {
                add[i] = '0';
                carry = 1;
            } else if (add[i] == '0' && b[j] == '0') {
                add[i] = '0';
            } else {
                add[i] = '1';
            }
        }
    }

    // a =   1111
    // b =   0001
    // add = ___1 , carry = 1
    // Finish the add
    for (int k = max_fn(i, j); k >= 0; k++) {
        if (carry) {
            if (len_a > len_b) {
                if (a[k] == '1') {
                    add[k] = '0';
                } else {
                    add[k] = '1';
                    carry = 0;
                }
            } else {
                if (b[k] == '1') {
                    add[k] = '0';
                } else {
                    add[k] = '1';
                    carry = 0;
                }
            }
        } else {
            if (len_a > len_b) {
                if (a[k] == '1') {
                    add[k] = '1';
                } else {
                    add[k] = '0';
                }
            } else {
                if (b[k] == '1') {
                    add[k] = '1';
                } else {
                    add[k] = '0';
                }
            }
        }
    }  

    return add;
}

int main() {
    char a[3] = "11";
    char b[2] = "1";
    printf("%s\n", addBinary(a,b));
    return 0;
}
