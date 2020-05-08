//Kernel with the same kind of structures as the GRIM-Filter kernel
//It is not exactly the same thing however (the original uses single bit operations)

#define SEQUENCES 64
#define BITVECTORS 32
#define THRESHOLD 100

#include "../runtime.h"

void grimfilter_kernel(int A[][100], int out[100]) {
    for (int i = 0; i < SEQUENCES; i++) {
        for (int j = 0; j < BITVECTORS; j++) {
            out[j] = out[j] + A[i][j];
        }
    }

    for (int j = 0; j < BITVECTORS; j++) {
        out[j] = out[j] > THRESHOLD;
    }
}
        
