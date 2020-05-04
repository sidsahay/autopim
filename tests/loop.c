int loop(int A[][100]) {
    int sum = 0;

    for (int i = 0; i < 20; i++) {
        for (int j = 0; j < 20; j++) {
            A[i][j] += 1;
        }
    }

    return sum;
}
