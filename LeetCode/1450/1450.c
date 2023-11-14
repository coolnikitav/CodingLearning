int busyStudent(int* startTime, int startTimeSize, int* endTime, int endTimeSize, int queryTime) {
    int num_of_students_at_query = 0;

    for (int i = 0; i < startTimeSize; i++) {
        if (startTime[i] <= queryTime && endTime[i] >= queryTime) {
            num_of_students_at_query++;
        }
    }

    return num_of_students_at_query++;
}
