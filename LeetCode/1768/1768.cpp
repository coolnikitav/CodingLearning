class Solution {
public:
    string mergeAlternately(string word1, string word2) {
        string output = "";
        int len1 = word1.length();
        int len2 = word2.length();
        for(int i = 0; i < ((len1 > len2) ? len2 : len1); i++){
            output += word1[i];
            output += word2[i];
        }
        if(len1 < len2){
            output += word2.substr(len1);
        }else if(len1 > len2){
            output += word1.substr(len2);
        }
        return output;
    }
};
