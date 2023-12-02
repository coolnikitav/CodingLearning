#include<iostream>

using namespace std;

class Solution {
    public:
        struct TreeNode {
            int val;
            TreeNode *left;
            TreeNode *right;
            TreeNode() : val(0), left(nullptr), right(nullptr) {}
            TreeNode(int x) : val(x), left(nullptr), right(nullptr) {}
            TreeNode(int x, TreeNode *left, TreeNode *right) : val(x), left(left), right(right) {}
        };

        struct TreeNode* searchBST(TreeNode* root, int val) {
            if (root == NULL) {
                return NULL;
            }

            if (root->val == val) {
                return root;
            } else if (root->val > val) {
                return searchBST(root->left, val);
            } else {
                return searchBST(root->right, val);
            }
        }
};

int main() {
    Solution test = Solution();
    Solution::TreeNode node1(1);
    Solution::TreeNode node3(3);
    Solution::TreeNode node2(2, &node1, &node3);
    Solution::TreeNode node7(7);
    Solution::TreeNode root1(4, &node2, &node7);

    Solution::TreeNode* result = test.searchBST(&root1, 2);
    cout << result->val << endl;
    return 0;
}
