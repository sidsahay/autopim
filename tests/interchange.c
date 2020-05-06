void trivial(int out[], int A[256][256]) {
    for (int i = 0; i < 32; i++) {
        for (int v = 0; v < 3; v++) {
            out[i] = out[i] + A[v][i];
        }
    }
}
