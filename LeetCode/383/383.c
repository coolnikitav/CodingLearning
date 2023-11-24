#include<stdio.h>
#include<stdbool.h>
#include<string.h>
#include<stdlib.h>

bool canConstruct(char * ransomNote, char * magazine){
    
    // create a map to store the frequency of char in ransomNote
    int map[26] = {0};
    
    // check what is in ransomNote and magazine
    while(*ransomNote){
        map[*ransomNote - 'a']++;
        ransomNote++;
    }
    while(*magazine){
        map[*magazine - 'a']--;
        magazine++;
    }
    
    // check if frequency of any char in ransomNote is greater than in magazine
    for(int i=0; i < 26; i++)
        if (map[i] > 0) return false;
    return true;
}

int main() {
    char ransom_note1[] = "aa";
    char magazine1[] = "aa";
    printf("Test 1:\n    Input: ransom_note = \"aa\", magazine = \"aa\"\n    Expected output: 1\n    Actual output: %d", canConstruct(ransom_note1, magazine1));

    return 0;
}
