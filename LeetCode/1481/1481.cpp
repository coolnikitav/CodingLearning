using namespace std;

typedef pair<int,int> freq_num;

unordered_map<int,int> create_freq_map(vector<int>& arr) {
    unordered_map<int,int> freq;

    for (int i = 0; i < arr.size(); i++) {
        if (freq.find(arr[i]) == freq.end()) {
            freq[arr[i]] = 1;
        } else {
            freq[arr[i]]++;
        }
    }

    return freq;
}

priority_queue<freq_num, vector<freq_num>, greater<freq_num>> create_pq(unordered_map<int,int> freq, vector<int>& arr) {
    priority_queue<freq_num, vector<freq_num>, greater<freq_num>> pq;
    for (auto key : freq) {
        pair<int,int> new_pair = make_pair(key.second, key.first);
        pq.push(new_pair);
    }
    return pq;
}

#include <iostream>
#include <unordered_map>
#include <queue>
using namespace std;

int findLeastNumOfUniqueInts(vector<int>& arr, int k) {
    unordered_map<int,int> freq;
    freq = create_freq_map(arr);

    priority_queue<freq_num, vector<freq_num>, greater<freq_num>> pq;
    pq = create_pq(freq, arr);

    while (k > 0) {
        if ((pq.top()).first > k) {
            k -= (pq.top()).first;
        } else {
            k -= (pq.top()).first;
            pq.pop();
        } 
    }
    return pq.size();
}

int main() {
    vector<int> arr1 = {5,5,4};
    cout << findLeastNumOfUniqueInts(arr1,1) << endl;

    vector<int> arr4 = {1,1};
    cout << findLeastNumOfUniqueInts(arr4,2) << endl;

    vector<int> arr3 = {2,4,1,8,3,5,1,3};
    cout << findLeastNumOfUniqueInts(arr3,3) << endl;

    vector<int> arr2 = {4,3,1,1,3,3,2};
    cout << findLeastNumOfUniqueInts(arr2,3) << endl;

    

    return -1;
}
