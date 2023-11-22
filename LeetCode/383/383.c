#include<stdio.h>
#include<stdbool.h>
#include<string.h>
#include<stdlib.h>

int* construct_frequency_map(char* word) {
    int* frequency_map = (int*)calloc(26, sizeof(int));

    for (int i = 0; i < strlen(word); i++) {
        frequency_map[word[i]-97]++;
    }

    return frequency_map;
}

bool canConstruct(char* ransomNote, char* magazine) {
    int* ransom_note_letter_frequency_map = construct_frequency_map(ransomNote);
    int* magazine_letter_frequency_map = construct_frequency_map(magazine);

    for (int i = 0; i < 26; i++) {
        if (ransom_note_letter_frequency_map[i] > magazine_letter_frequency_map[i]) {
                free(ransom_note_letter_frequency_map);
                free(magazine_letter_frequency_map);
            return false;
        }
    }
    
    free(ransom_note_letter_frequency_map);
    free(magazine_letter_frequency_map);
    return true;
}

int main() {
    char* ransom_note1 = "aa";
    char* magazine1 = "aa";
    printf("Test 1:\n    Input: ransom_note = \"aa\", magazine = \"aa\"\n    Expected output: 1\n    Actual output: %s", canConstruct(ransom_note1, magazine1));

    return 0;
}
