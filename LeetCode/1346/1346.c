bool checkIfExist(int* arr, int arrSize){
    int hash_map[2001] = {0};

    for (int i = 0; i < arrSize; i++) {
           hash_map[arr[i]+1000] = i+1; 
    }

    for (int i = 0; i < arrSize; i++) {
        if (arr[i] <= 500 && arr[i] >= -500) {
            if (hash_map[2*arr[i]+1000] != 0 && hash_map[2*arr[i]+1000] != i+1) {
                return true;
            }
        }
    }

    return false;
}
