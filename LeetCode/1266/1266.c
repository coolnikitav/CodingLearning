int minTimeToVisitAllPoints(int** points, int pointsSize, int* pointsColSize) {
    int count=0;
    for(int i=0;i<pointsSize-1;i++) {
        int x=abs(points[i+1][0]-points[i][0]);
        int y=abs(points[i+1][1]-points[i][1]);
        while(x!=0&&y!=0) {
            x--;
            y--;
            count++;
        }
        count=count+x+y;   
    }
    return count;
}
