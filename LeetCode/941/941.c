bool validMountainArray(int* arr, int arrSize){
    if (arrSize < 3) {
        return false;
    }

    int index = 1;
    bool ascending = false;
    bool descending = false;

    while (index < arrSize-1 && arr[index] > arr[index-1]) {
        index++;
        ascending = true;
    }

    while (index < arrSize && arr[index] < arr[index-1]) {
        index++;
        descending = true;
    }

    if (index == arrSize && ascending && descending) {
        return true;
    }

    return false;
}
