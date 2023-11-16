bool check_students_for_sandwich(int* students, int studentsSize, int sandwich) {
    for (int i = 0; i < studentsSize; i++) {
        if (sandwich == students[i]) {
            students[i] = -1;
            return true;
        }
    }
    return false;
}

int countStudents(int* students, int studentsSize, int* sandwiches, int sandwichesSize) {
    int num_students_unable_to_eat = studentsSize;
    int curr_sandwich_index = 0;
    int curr_sandwich;

    while(curr_sandwich_index < sandwichesSize) {
        curr_sandwich = sandwiches[curr_sandwich_index];
        if (check_students_for_sandwich(students, studentsSize, curr_sandwich)) {
            curr_sandwich_index++;
            num_students_unable_to_eat--;
        } else {
            break;
        }
    }

    return num_students_unable_to_eat;
}
