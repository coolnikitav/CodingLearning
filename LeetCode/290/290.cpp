#include<iostream>
#include<map>

using namespace std;

class Solution {
    public:
        int find_next_index(string& s, int& idx) {
            while (idx < s.size() && s[idx] != ' ') {
                idx++;
            }
            return idx;
        }

        bool word_pattern(string pattern, string s) {
            map<char,string> word_map;
            int prev_idx = 0;
            int next_idx = 0;

            for (int i = 0; i < pattern.size(); i++) {
                string word = s.substr(prev_idx, find_next_index(s,(++next_idx)));
                cout << pattern[i] << " " << word << endl;

                if (word_map.find(pattern[i]) == word_map.end()) {
                    word_map[pattern[i]] = word;
                    prev_idx = next_idx;
                } else {
                    if (word_map[pattern[i]] != word) {
                        return false;
                    }
                }
            }

            return true;
        }
};

int main() {
    Solution test = Solution();

    string pattern1 = "abba";
    string s1 = "dog cat cat dog";
    cout << test.word_pattern(pattern1,s1) << endl;

    string pattern2 = "abba";
    string s2 = "dog cat cat fish";
    //cout << test.word_pattern(pattern2,s2) << endl;

    string pattern3 = "aaaa";
    string s3 = "dog cat cat dog";
    //cout << test.word_pattern(pattern3,s3) << endl;

    return 0;
}
