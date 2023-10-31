class Solution {
public:
    int maxLengthBetweenEqualCharacters(string s) {
        unordered_map<char, int> index;
        int ans = -1;

        for (int i = 0; i < s.size(); i++) {
            if (index.find(s[i]) != index.end()) {
                ans = max(ans, i - index[s[i]] - 1);
            } else {
                index[s[i]] = i;
            }
        }

        return ans;
    }
};
