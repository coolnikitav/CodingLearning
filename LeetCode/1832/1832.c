#include<stdio.h>
#include<stdbool.h>

bool check_if_alphabet_full(int* alphabet) {
    for (int i = 0; i < 26; i++) {
        if (alphabet[i] == 0) {
            return false;
        }
    }

    return true;
}

bool checkIfPangram(char* sentence) {
    int alphabet[26] = {0};

    int idx = 0;
    while (sentence[idx] != '\0') {
        alphabet[sentence[idx]-'a'] = 1;
        idx++;
    }

    return check_if_alphabet_full(alphabet);
}

int main() {
    char sentence1[] = "thequickbrownfoxjumpsoverthelazydog";
    printf("%d\n", checkIfPangram(sentence1));

    char sentence2[] = "leetcode";
    printf("%d\n", checkIfPangram(sentence2));

    char sentence3[] = "anmt";
    printf("%d\n", checkIfPangram(sentence3));

    return 0;
}
