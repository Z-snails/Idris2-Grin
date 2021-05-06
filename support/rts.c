#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

extern int64_t _heat_ptr;
int64_t grinMain();

void __runtime_error(int64_t code) {
    exit(code);
}

int main() {
    int64_t* heap = malloc(100*1024*1024);
    _heat_ptr = heap
    grinMain();
    free(heap);
    return 0;
}