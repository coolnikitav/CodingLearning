#include<iostream>
#include<map>

using namespace std;

class Solution {
    public:
        int& find_next_index(string& s, int& idx) {
            while (idx < s.size() && s[idx] != ' ') {
                idx++;
            }
            return idx;
        }

        string get_substring(string& s, int& start_idx, int& end_idx) {
            if (end_idx > s.size()) {
                return "Invalid index";
            }
            return s.substr(start_idx, end_idx-start_idx);
        }

        bool word_pattern(string pattern, string s) {
            map<char,string> pattern_map;
            map<string,char> s_map;
            int prev_idx = 0;
            int next_idx = 0;

            for (int i = 0; i < pattern.size(); i++) {
                string word = get_substring(s, prev_idx, find_next_index(s,next_idx));
                if (word == "Invalid index") {
                    return false;
                }
                prev_idx = ++next_idx;

                if (pattern_map.find(pattern[i]) == pattern_map.end()) {
                    pattern_map[pattern[i]] = word;
                } else {
                    if (pattern_map[pattern[i]] != word) {
                        return false;
                    }
                }

                if (s_map.find(word) == s_map.end()) {
                    s_map[word] = pattern[i];
                } else {
                    if (s_map[word] != pattern[i]) {
                        return false;
                    }
                }
            }

            if(next_idx < s.size()) {
                return false;
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
    cout << test.word_pattern(pattern2,s2) << endl;

    string pattern3 = "aaaa";
    string s3 = "dog cat cat dog";
    cout << test.word_pattern(pattern3,s3) << endl;

    string pattern4 = "abba";
    string s4 = "dog dog dog dog";
    cout << test.word_pattern(pattern4,s4) << endl;

    string pattern5 = "aaa";
    string s5 = "aa aa aa aa";
    cout << test.word_pattern(pattern5,s5) << endl;

    string pattern6 = "jquery";
    string s6 = "jquery";
    cout << test.word_pattern(pattern6,s6) << endl;

    return 0;
}
