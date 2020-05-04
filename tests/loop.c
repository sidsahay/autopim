int loop(int A[100][100], int B[100][100], int C[100][100]) {
    int sum = 0;

    for (int i = 0; i < 20; i++) {
        for (int j = 0; j < 40; j++) {
            A[i][j] = B[i][j] + C[i][j];
            sum += A[i][j];
        }
    }
}
