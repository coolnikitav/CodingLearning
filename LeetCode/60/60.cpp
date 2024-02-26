#include <iostream>
#include <vector>
#include <string>

using namespace std;

class Solution {
public:
    int permutations(int n) {
        int fact = 1;
        while (n > 0) {
            fact *= n;
            n--;
        }
        return fact;
    }

    vector<int> create_comb(int permutations, int n) {
        vector<int> comb(n);
        int index = n;

        for (int i = 0; i < n; i++) {
            comb[i] = permutations / index;
            permutations /= index;
            index--;
        }
        
        return comb;
    }

    vector<int> create_n_vector(int n) {
        vector<int> n_vector(n);

        for (int i = n-1; i >=0; i--) {
            n_vector[i] = n;
            n--;
        }

        return n_vector;
    }

    string getPermutation(int n, int k) {
        vector<int> comb = create_comb(permutations(n),n);
        vector<int> n_vector = create_n_vector(n);
        vector<int> indexes(n);
        int index = 0;

        // first num is 1,2,3,4..n
        // this loop tells us which num it will be
        for (int i = 0; i < n; i++) {
            while ((index+1) * comb[i] < k) {
                index++;
            }
            indexes[i] = index;
            if (index > 0) {
                k -= index * comb[i];
            }
            index = 0;
        }

        string output = "";
        int index_temp;
        int n_temp;
        for (int i = 0; i < n; i++) {
            index_temp = indexes[i];
            n_temp = n_vector[index_temp];
            output.append(to_string(n_temp));
            n_vector.erase(n_vector.begin()+index_temp);
        }

        return output;
    }
};

int main() {
    Solution test = Solution();

    cout << test.getPermutation(3,3) << endl;
    cout << test.getPermutation(4,9) << endl;
    cout << test.getPermutation(3,1) << endl;

    return -1;
}
