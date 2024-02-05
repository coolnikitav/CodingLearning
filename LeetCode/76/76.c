#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

char* create_return_string(char* s, int i, int j) {
    char* return_string = (char*)malloc((j-i+1) * sizeof(char));
    for (int idx = 0; idx < j-i; idx++) {
        return_string[idx] = s[idx+i];
    }
    return_string[j-i] = '\0';
    return return_string;
}

bool t_traversed(char* t) {
    for (int i = 0; i < strlen(t); i++) {
        if (t[i] != '1') {
            return false;
        }
    }
    return true;
}

void check(char c, char* t) {
    for (int i = 0; i < strlen(t); i++) {
        if (t[i] == c) {
            t[i] = '1'; // in case of duplicates
            return;
        }
    }
}

bool letter_in_string(char c, char* s) {
    for (int i = 0; i < strlen(s); i++) {
        if (s[i] == c) {
            return true;
        }
    }
    return false;
}

char* minWindow(char* s, char* t) {
    int s_len = strlen(s);
    int t_len = strlen(t);

    char* t_copy = (char*)malloc((t_len+1) * sizeof(char));
    strcpy(t_copy,t);

    int min_len = s_len;
    int min_beg = 0;
    int min_end = 0;

    if (t_len > s_len) {
        return "";
    }

    // Naive/brute force
    for (int i = 0; i < s_len; i++) {
        if (letter_in_string(s[i],t)) {
            for (int j = i; j < s_len; j++) {
                if (j-i < min_len) {
                    check(s[j],t_copy);
                    if (t_traversed(t_copy)) {                        
                        min_len = j-i+1;
                        min_beg = i;
                        min_end = j+1;
                        break;
                    }
                }
            }
            strcpy(t_copy,t);
        }
    }
    free(t_copy);
    return create_return_string(s,min_beg,min_end);
}

int main() {
    printf("%s\n", minWindow("ADOBECODEBANC","ABC"));
    printf("%s\n", minWindow("a","a"));
    printf("%s\n", minWindow("a","b"));
    printf("%s\n", minWindow("a","aa"));
    return -1;
}
