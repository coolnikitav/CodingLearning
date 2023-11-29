#include<stdio.h>
#include<string.h>

void adjust_min_length(char* s, int s_length, int curr_idx, int* min_length) {
    (*min_length) -= 2;

    int offset = 1;
    while ((curr_idx-offset) >= 0 && (curr_idx+1+offset) < s_length && ((s[curr_idx-offset] == 'A' && s[curr_idx+1+offset] == 'B') || (s[curr_idx-offset] == 'C' && s[curr_idx+1+offset] == 'D'))) {
        (*min_length) -= 2;
        offset++;
    }
}

int minLength(char* s) {
    int s_length = strlen(s);
    int min_length = s_length;

    for (int i = 0; i < s_length-1; i++) {
        if ((s[i] == 'A' && s[i+1] == 'B') || (s[i] == 'C' && s[i+1] == 'D')) {
            adjust_min_length(s, s_length, i, &min_length);
        }
    }

    return min_length;
}

int main() {
    char s1[9] = "ABFCACDB";
    printf("%d\n", minLength(s1));

    char s2[6] = "ACBBD";
    printf("%d\n", minLength(s2));

    char s3[11] = "CCDAABBDCD";
    printf("%d\n", minLength(s3));

    return 0;
}