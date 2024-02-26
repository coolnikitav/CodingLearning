#include <iostream>

using namespace std;

struct TreeNode {
   int val;
    TreeNode *left;
    TreeNode *right;
    TreeNode() : val(0), left(nullptr), right(nullptr) {}
    TreeNode(int x) : val(x), left(nullptr), right(nullptr) {}
    TreeNode(int x, TreeNode *left, TreeNode *right) : val(x), left(left), right(right) {}
 };

class Solution {
public:
    bool isSameTree(TreeNode* p, TreeNode* q) {
        if (p == nullptr || q == nullptr) {
            return p == q;
        }
        if (p->val != q->val) {
            return false;
        }
        bool L = isSameTree(p->left, q->left);
        bool R = isSameTree(p->right, q->right);
        return L && R;
    }
};

int main() {
    Solution test = Solution();
    // Test #1 
    // p
    TreeNode two1p = TreeNode(2);
    TreeNode three1p = TreeNode(3);
    TreeNode root_one1p = TreeNode(1,&two1p,&three1p);
    // q
    TreeNode two1q = TreeNode(2);
    TreeNode three1q = TreeNode(3);
    TreeNode root_one1q = TreeNode(1,&two1q,&three1q);
 
    cout << test.isSameTree(&root_one1p, &root_one1q) << endl;
    
    // Test #2 
    // p
    two1p = TreeNode(2);
    root_one1p = TreeNode(1,&two1p,nullptr);
    // q
    two1q = TreeNode(2);
    root_one1q = TreeNode(1,nullptr,&two1q);

    cout << test.isSameTree(&root_one1p, &root_one1q) << endl;

    // Test #3
    // p
    two1p = TreeNode(2);
    TreeNode one1p = TreeNode(3);
    root_one1p = TreeNode(1,&two1p,&one1p);
    // q
    two1q = TreeNode(2);
    TreeNode one1q = TreeNode(3);
    root_one1q = TreeNode(1,&one1q,&two1q);

    cout << test.isSameTree(&root_one1p, &root_one1q) << endl;

    return -1;
} 
