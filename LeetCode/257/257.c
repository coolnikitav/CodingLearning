#include<stdio.h>
#include<stdlib.h>
#include<string.h>

struct TreeNode {
    int val;
    struct TreeNode *left;
    struct TreeNode *right;
};

//Recursive helper function
void dfs(struct TreeNode* node, char** paths, char* path, int path_len, int* path_num){
	if (!node) return;
	
	//Add current node in path
	int len = snprintf(path + path_len, 14, "%d->", node->val); //6("%d->")+1('\0'); len is strlen("%d->")
	path_len += len; //update path len
	
	if (!node->left && !node->right){ //Leaf node, add path to paths
		 paths[*path_num] = (char*)malloc(sizeof(char)*(path_len+1-2)); //1 for '\0' and ex:"1->\0" => "1"
		 memcpy(paths[*path_num], path, path_len+1-2-1); //path="1->\0", only need to copy "1" to paths[]
		 paths[*path_num][path_len+1-2-1] = '\0'; //paths[] = "1\0"
		 (*path_num)++;
	}
	
	dfs(node->left, paths, path, path_len, path_num);
	dfs(node->right, paths, path, path_len, path_num);
	
}

char ** binaryTreePaths(struct TreeNode* root, int* returnSize){
	char** paths=(char**)malloc(sizeof(char*)*37);//1+2+4+8+16+32+"37" = 100 => 37 is the max number of leaf nodes, which implies max path num is 37.
	char* path=(char*)malloc(sizeof(char)*599); // 100*4("-100")+99*2("->")+1('\0)
	*returnSize = 0;
	
	dfs(root, paths, path, 0, returnSize);
	
	free(path);
	return paths;
}

void free_paths(char** paths, int size) {
	for (int i = 0; i < size; i++) {
		free(paths[i]);
	}
	free(paths);
}

int main() {
    struct TreeNode* root = (struct TreeNode*)malloc(sizeof(struct TreeNode));
    struct TreeNode* node2 = (struct TreeNode*)malloc(sizeof(struct TreeNode));
    struct TreeNode* node3 = (struct TreeNode*)malloc(sizeof(struct TreeNode));
    struct TreeNode* node5 = (struct TreeNode*)malloc(sizeof(struct TreeNode));
    root->val = 1;
    node2->val = 2;
    node3->val = 3;
    node5->val = 5;
    root->left = node2;
    root->right = node3;
    node2->right = node5;
    int returnSize;

	char** paths = binaryTreePaths(root, &returnSize);

    for (int i = 0; i < returnSize; i++) {
		printf("%s\n", paths[i]);
	}

	free_paths(paths, returnSize);
	free(root);
	free(node2);
	free(node3);
	free(node5);

    return 0;
}