int* constructRectangle(int area, int* returnSize){
    int width = (int)sqrt(area);

    while (area%width != 0) {
        width--;
    }

    *returnSize = 2;
    int* dimensions = (int*)malloc(*returnSize * sizeof(int));
    dimensions[0] = area/width;
    dimensions[1] = width;

    return dimensions;
}
