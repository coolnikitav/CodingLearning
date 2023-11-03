class Solution {
public:
    bool detectCapitalUse(string word) {
        if (word.size() == 1) {
            return true;
        }
        bool all_capitals = false;
        bool no_capitals = false;
        bool first_capital = false;
        if (isupper(word[0])) {
            if (isupper(word[1])) {
                all_capitals = true;
            } else {
                first_capital = true;
            }
        } else {
            if (islower(word[1])) {
                no_capitals = true;
            } else {
                return false;
            }
        }

        for (int i = 2; i < word.size(); i++) {
            if (all_capitals) {
                if (islower(word[i])) {
                    return false;
                }
            } else {
                if (isupper(word[i])) {
                    return false;
                }
            }
        }
        return true;
    }
};
