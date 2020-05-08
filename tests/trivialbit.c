#inlude "../runtime.h"

void trivial(int out[], int A[256][256]) {
    for (int i = 0; i < 32; i++) {
        for (int v = 0; v < 3; v++) {
            int t = A[i][v];
            out[v] = 32 * (out[v] & t);
        }
    }
}
