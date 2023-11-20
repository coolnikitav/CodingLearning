#include<stdio.h>
#include<stdbool.h>

bool checkZeroOnes(char* s) {
    int curr_num_of_ones = 0, max_num_of_ones = 0, curr_num_of_zeroes = 0, max_num_of_zeroes = 0;

    int idx = 0;
    while (s[idx] != '\0') {
        if (s[idx] == '1') {
            curr_num_of_zeroes = 0;
            curr_num_of_ones++;
            if (curr_num_of_ones > max_num_of_ones) {
                max_num_of_ones = curr_num_of_ones;
            }
        } else {
            curr_num_of_ones = 0;
            curr_num_of_zeroes++;
            if (curr_num_of_zeroes > max_num_of_zeroes) {
                max_num_of_zeroes = curr_num_of_zeroes;
            }
        }
        idx++;
    }

    return max_num_of_ones > max_num_of_zeroes;
}

int main() {
    char* s1 = "1101";
    printf("Test 1 : \"1101\" : %d\n", checkZeroOnes(s1));

    char* s2 = "111000";
    printf("Test 2 : \"111000\" : %d\n", checkZeroOnes(s2));

    char* s3 = "110100010";
    printf("Test 3 : \"110100010\" : %d\n", checkZeroOnes(s3));

    char* s4 = "1111";
    printf("Test 4 : \"1111\" : %d\n", checkZeroOnes(s4));

    char* s5 = "0000";
    printf("Test 5 : \"0000\" : %d\n", checkZeroOnes(s5));

    char* s6 = "1";
    printf("Test 6 : \"1\" : %d\n", checkZeroOnes(s6));

    return 0;
}
