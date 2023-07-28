class Solution {
public:
    bool isSubsequence(string s, string t) {
        if (s == "") {
            return true;
        }

        int idx = 0;
        for (int i = 0; i < t.length(); i++) {
            if (s[idx] == t[i]) { //if a letter of s is found in t
                idx++;
                if (idx == s.length()) { //if we went through s before going through t
                    return true;
                }
            }
        }
        return false;
    }
};
