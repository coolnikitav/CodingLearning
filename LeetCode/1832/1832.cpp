#include<iostream>
#include<unordered_map>

using namespace std;

class Solution {
    public:
        bool check_if_pangram(string sentence) {
            unordered_map<char,int> letters;

            for (int i = 0; i < sentence.size(); i++) {
                letters[sentence[i]] = 1;
            }

            return (letters.size() == 26) ? true : false;
        }
};

int main() {
    Solution test = Solution();

    string sentence1 = "thequickbrownfoxjumpsoverthelazydog";
    cout << test.check_if_pangram(sentence1) << endl;

    string sentence2 = "leetcode";
    cout << test.check_if_pangram(sentence2) << endl;

    return 0;
}
