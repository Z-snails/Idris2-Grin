#include <gmp.h>

mpz_t* _prim_add_Integer(mpz_t* x, mpz_t* y) {
    mpz_t ret;
    mpz_init(ret);
    mpz_add(ret, x, y);
    return ret;
}

mpz_t* _prim_sub_Integer(mpz_t* x, mpz_t* y) {
    mpz_t ret;
    mpz_init(ret);
    mpz_sub(ret, x, y);
    return ret;
}

mpz_t* _prim_new_Integer(char* str) {
    mpz_t ret;
    mpz_init_set_str(ret, str, 10);
    return ret;
}

void _prim_clear_Integer(mpz_t* x) {
    mpz_clear(x);
}
