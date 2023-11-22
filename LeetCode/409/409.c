#include<stdio.h>
#include<stdbool.h>

int longestPalindrome(char* s) {
    int letter_frequency_map[58] = {0};
    int longest_palindrome_length = 0;
    bool more_than_one_letter = false;

    int idx = 0;
    while (s[idx] != '\0') {
        letter_frequency_map[s[idx]-65]++;

        if (s[idx] != s[0]) {
            more_than_one_letter = true;
        }

        idx++;
    }

    bool one_odd_frequency_used = false;

    for (int i = 0; i < 58; i++) {
        int letter_frequency = letter_frequency_map[i];
        if (more_than_one_letter) {
            if (letter_frequency % 2 == 1) {
                one_odd_frequency_used = true;
                longest_palindrome_length += (letter_frequency-1);
            } else {
                longest_palindrome_length += letter_frequency;
            }
        } else {
            if (letter_frequency != 0) {
                return letter_frequency;
            }
        }
    }
    if (one_odd_frequency_used) {
        longest_palindrome_length += 1;
    }

    return longest_palindrome_length;
}

int main() {
    char* s1 = "abccccdd";
    printf("%d\n", longestPalindrome(s1));

    char* s2 = "a";
    printf("%d\n", longestPalindrome(s2));

    char* s3 = "ccc";
    printf("%d\n", longestPalindrome(s3));

    char* s4 = "bananas";
    printf("%d\n", longestPalindrome(s4));

    char* s5 = "zeusnilemacaronimaisanitratetartinasiaminoracamelinsuez";
    printf("%d\n", longestPalindrome(s5));

    char* s6 = "civilwartestingwhetherthatnaptionoranynartionsoconceivedandsodedicatedcanlongendureWeareqmetonagreatbattlefiemldoftzhatwarWehavecometodedicpateaportionofthatfieldasafinalrestingplaceforthosewhoheregavetheirlivesthatthatnationmightliveItisaltogetherfangandproperthatweshoulddothisButinalargersensewecannotdedicatewecannotconsecratewecannothallowthisgroundThebravelmenlivinganddeadwhostruggledherehaveconsecrateditfaraboveourpoorponwertoaddordetractTgheworldadswfilllittlenotlenorlongrememberwhatwesayherebutitcanneverforgetwhattheydidhereItisforusthelivingrathertobededicatedheretotheulnfinishedworkwhichtheywhofoughtherehavethusfarsonoblyadvancedItisratherforustobeherededicatedtothegreattdafskremainingbeforeusthatfromthesehonoreddeadwetakeincreaseddevotiontothatcauseforwhichtheygavethelastpfullmeasureofdevotionthatweherehighlyresolvethatthesedeadshallnothavediedinvainthatthisnationunsderGodshallhaveanewbirthoffreedomandthatgovernmentofthepeoplebythepeopleforthepeopleshallnotperishfromtheearth";
    printf("%d\n", longestPalindrome(s6));

    char* s7 = "aaaCCC";
    printf("%d\n", longestPalindrome(s7));

    return 0;
}
