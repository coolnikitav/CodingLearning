int findPoisonedDuration(int* timeSeries, int timeSeriesSize, int duration) {
    int total_duration = 0;
    for (int i = 0; i < timeSeriesSize-1; i++) {
        total_duration += (timeSeries[i+1] - timeSeries[i]) > duration ? duration : (timeSeries[i+1] - timeSeries[i]);
    }

    total_duration += duration;     // The last shot always has the full duration

    return total_duration;
}
