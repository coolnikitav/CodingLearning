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

        TreeNode* searchBST(TreeNode* root, int val) {
            if (!root) {
                return NULL;
            }

            if (root->val == val) {
                return root;
            }

            TreeNode* left_node = searchBST(root->left, val);
            TreeNode* right_node = searchBST(root->right, val);

            return left_node ? left_node : right_node;
        }
};

int main() {
    Solution test = Solution();
    Solution::TreeNode node1(1);
    Solution::TreeNode node3(3);
    Solution::TreeNode node2(2, node1, node3);
    Solution::TreeNode node7(7);
    Solution::TreeNode root1(4, node2, node7);
    return 0;
}
