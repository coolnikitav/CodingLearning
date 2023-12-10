#include<iostream>
#include<vector>

using namespace std;

class Solution {
    public:
        vector<int> decode(vector<int>& encoded, int first) {
            vector<int> decoded = {first};

            for (int i = 0; i < encoded.size(); i++) {
                decoded.push_back(encoded[i] ^ decoded[i]);
            }

            return decoded;
        }

        void print_vector(vector<int> nums) {
            cout << "{";
            for (int i = 0; i < nums.size()-1; i++) {
                cout << nums[i] << ", ";
            }
            cout << nums[nums.size()-1] << "}" << endl;
        }
};

int main() {
    Solution test = Solution();

    vector<int> encoded1 = {1,2,3};
    test.print_vector(test.decode(encoded1,1));

    vector<int> encoded2 = {6,2,7,3};
    test.print_vector(test.decode(encoded2,4));

    return 0;
}