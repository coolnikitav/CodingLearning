#include <iostream>
#include <unordered_map>
#include <queue>
using namespace std;

unordered_map<int,int> create_freq_map(vector<int>& arr) {
    unordered_map<int,int> freq;

    for (int num : arr) {
        freq[num]++;
    }

    return freq;
}

priority_queue<int, vector<int>, greater<int>> create_pq(unordered_map<int,int> freq, vector<int>& arr) {
    priority_queue<int, vector<int>, greater<int>> pq;
    for (auto item : freq) {
        pq.push(item.second);
    }
    return pq;
}



int findLeastNumOfUniqueInts(vector<int>& arr, int k) {
    unordered_map<int,int> freq;
    freq = create_freq_map(arr);

    priority_queue<int, vector<int>, greater<int>> pq;
    pq = create_pq(freq, arr);

    while(k>0){
        k=k-pq.top();
        if(k>=0){
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
