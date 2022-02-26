#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint8_t* _heap_ptr;

void grinMain();

void _prim_int_print(int64_t x) {
    printf("%ld", x);
}

void __runtime_error(int64_t code) {
    free(_heap_ptr);
    exit(code);
}

int main() {
    _heap_ptr = calloc(sizeof(uint8_t), 4096 * 1024);
    grinMain();
    printf("\n");
}