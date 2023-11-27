#include<stdlib.h>

struct TreeNode {
    int val;
    struct TreeNode *left;
    struct TreeNode *right;
};
 
double* averageOfLevels(struct TreeNode* root, int* returnSize){
    double* result = (double*)calloc(10000, sizeof(double));
    struct TreeNode* queue[10000];
    int front = 0, back = 0;
    *returnSize = 0;

    queue[back] = root;
    back++;

    while (front < back) {
        double sum = 0.0;
        int len = back - front;
        int cur_back = back;

        while (front < cur_back) {
            struct TreeNode* curr_node = queue[front];
            front++;

            if (curr_node->left) {
                queue[back] = curr_node->left;
                back++;
            }

            if (curr_node->right) {
                queue[back] = curr_node->right;
                back++;
            }

            sum += curr_node->val;
        }
        result[*returnSize] = sum/len;
        (*returnSize)++;
    }

    return result;
}

int main() {
    struct TreeNode* root = (struct TreeNode*)malloc(sizeof(struct TreeNode));
    struct TreeNode* node9 = (struct TreeNode*)malloc(sizeof(struct TreeNode));
    struct TreeNode* node20 = (struct TreeNode*)malloc(sizeof(struct TreeNode));
    struct TreeNode* node15 = (struct TreeNode*)malloc(sizeof(struct TreeNode));
    struct TreeNode* node7 = (struct TreeNode*)malloc(sizeof(struct TreeNode));

    root->val = 3;
    node9->val = 9;
    node20->val = 20;
    node15->val = 15;
    node7->val = 7;

    root->left = node9;
    root->right = node20;
    node20->left = node15;
    node20->right = node7;

    int return_size;

    averageOfLevels(root, &return_size);

    free(root);
    free(node9);
    free(node20);
    free(node15);
    free(node7);
    return 0;
}
