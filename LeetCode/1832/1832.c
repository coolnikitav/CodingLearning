#include<stdio.h>
#include<stdbool.h>

bool check_if_alphabet_full(char* alphabet) {
    int idx = 0;

    while (alphabet[idx] != '\0') {
        if (alphabet[idx] == '0') {
            return false;
        }
        idx++;
    }

    return true;
}

bool checkIfPangram(char* sentence) {
    char alphabet[26] = {'0'};

    int idx = 0;
    while (sentence[idx] != '\0') {
        alphabet[sentence[idx]-97] = '1';
        idx++;
    }

    return check_if_alphabet_full(alphabet);
}

int main() {
    char* sentence1 = "thequickbrownfoxjumpsoverthelazydog";
    printf("%d\n", checkIfPangram(sentence1));

    char* sentence2 = "leetcode";
    printf("%d\n", checkIfPangram(sentence2));

    return 0;
}
