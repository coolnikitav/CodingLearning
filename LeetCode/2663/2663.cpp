#include<iostream>
#include<vector>
#include<unordered_map>

using namespace std;

class Solution {
public:
    unordered_map<int,int> convert_vector_to_map(vector<vector<int>>& items) {
        unordered_map<int,int> map;
        
        for (int i = 0; i < items.size(); i++) {
            map[items[i][0]] = items[i][1];
        }

        return map;
    }

    void merge_vector_to_map(unordered_map<int,int>& map, vector<vector<int>>& items) {
        for (int i = 0; i < items.size(); i++) {
            map[items[i][0]] += items[i][1];
        }
    }

    void insert_item_in_order(vector<vector<int>>& items, vector<int> item) {
        int idx = 0;
        int items_size = items.size();

        while (idx < items_size && item[0] > items[idx][0]) {
            idx++;
        }
        items.insert(items.begin() + idx, item);
    }

    vector<vector<int>> convert_map_to_vector(unordered_map<int,int>& map) {
        vector<vector<int>> items;
        
        for (auto i : map) {
            vector<int> item {i.first, i.second};

            if (items.size() == 0) {
                items.insert(items.begin(), item);
            } else {
                insert_item_in_order(items, item);
            }
        }

        return items;
    }

    void print_2d_vector(vector<vector<int>>& items) {
        for (int i = 0; i < items.size(); i++) {
            for (int j = 0; j < items[0].size(); j++) {
                cout << items[i][j] << endl;
            }
        }
    }

    vector<vector<int>> mergeSimilarItems(vector<vector<int>>& items1, vector<vector<int>>& items2) {
        if (items1.size() > items2.size()) {
            unordered_map<int,int> items1_map = convert_vector_to_map(items1);
            merge_vector_to_map(items1_map, items2);
            return convert_map_to_vector(items1_map);
        } else {
            unordered_map<int,int> items2_map = convert_vector_to_map(items2);            
            merge_vector_to_map(items2_map, items1);
            return convert_map_to_vector(items2_map);
        }
    }
};

int main() {
    Solution test = Solution();
    vector<vector<int>> items1 {{1,1},{4,5},{3,8}};
    vector<vector<int>> items2 {{3,1},{1,5}};
    vector<vector<int>> merged_items = test.mergeSimilarItems(items1, items2);
    test.print_2d_vector(merged_items);

    return 0;
}