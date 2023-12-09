#include<iostream>
#include<vector>

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

    void tree_to_vector(TreeNode* root, vector<TreeNode*>& nodes) {
        if (!root) {
            return;
        }

        tree_to_vector(root->left, nodes);
        nodes.push_back(root);
        tree_to_vector(root->right, nodes);
    }

    TreeNode* increasingBST(TreeNode* root) {
        // in order traversal
        vector<TreeNode*> nodes;
        tree_to_vector(root, nodes);

        for (int i = 0; i < nodes.size()-1; i++) {
            nodes[i]->left = nullptr;
            nodes[i]->right = nodes[i+1];
        }

        if(!nodes.empty()) {
            nodes.back()->left = nullptr;
            nodes.back()->right = nullptr;
        }

        return nodes.empty() ? nullptr : nodes[0];
    }

    void print_tree(TreeNode* root) {
        if (!root) {
            return;
        }

        print_tree(root->left);
        cout << root->val << endl;
        print_tree(root->right);
    }
};

int main() {
    Solution test = Solution();

    Solution::TreeNode node1(1);
    Solution::TreeNode node2(2, &node1, nullptr);
    Solution::TreeNode node4(4);
    Solution::TreeNode node3(3, &node2, &node4);
    Solution::TreeNode node7(7);
    Solution::TreeNode node9(9);
    Solution::TreeNode node8(8, &node7, &node9);
    Solution::TreeNode node6(6, nullptr, &node8);
    Solution::TreeNode node5(5, &node3, &node6);
    test.print_tree(&node5);
    cout << "Created all nodes" << endl;

    Solution::TreeNode* result = test.increasingBST(&node5);
    cout << "Got the result" << endl;
    test.print_tree(result);
    cout << "Printed the result" << endl;

    return 0;
}
