class Solution {
public:
    bool isVowel(char s) {
        if (s == 'a' || s == 'e' || s == 'i' || s == 'o' || s == 'u') {
            return true;
        }
        return false;
    }

    int maxVowels(string s, int k) {
        int vowelLength = 0;
        int tempLength = 0;

        for (int i = 0; i < k; i++) {
            if (isVowel(s[i])) {
                tempLength++;
            }
        }

        vowelLength = tempLength;

        for (int i = k; i < s.length(); i++) {
           if (isVowel(s[i]) && !isVowel(s[i-k])) {
               tempLength++;
               if (tempLength > vowelLength) {
                   vowelLength = tempLength;
               }
           } else if (!isVowel(s[i]) && isVowel(s[i-k])) {
               tempLength--;
           }
        }
        return vowelLength;
    }
};
