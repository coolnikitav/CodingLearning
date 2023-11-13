#include<stdio.h>
#include<stdbool.h>
#include<string.h>

bool check_if_word_palindrome(char* word) {
    int length = strlen(word);

    for (int left = 0, right = length-1; left < right; left++, right--) {
        if (word[left] != word[right]) {
            return false;
        }
    }

    return true;
}

char* firstPalindrome(char** words, int wordsSize) {
    for (int i = 0; i < wordsSize; i++) {
        if (check_if_word_palindrome(words[i])) {
            return words[i];
        }
    }

    return "";
}

int main() {
    printf("%d\n", check_if_word_palindrome("ada"));
    printf("%d\n", check_if_word_palindrome("adfa"));

    char* words1[5] = {"abc","car","ada","racecar","cool"};
    char* words2[2] = {"notapalindrome","racecar"};
    char* words3[2] = {"def","ghi"};

    printf("Test 1: %s\n", firstPalindrome(words1, 5));
    printf("Test 2: %s\n", firstPalindrome(words2, 2));
    printf("Test 3: %s\n", firstPalindrome(words3, 2));

    return 0;
}
