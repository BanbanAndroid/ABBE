#include <pbc/pbc.h>
#include <pbc/pbc_test.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include "math.h"

void pbc_mpz_urandomb(mpz_t z, unsigned int bits)
{
    mpz_t limit;
    mpz_init(limit);
    mpz_setbit(limit, bits);
    pbc_mpz_random(z, limit);
    mpz_clear(limit);
}

size_t readConfig(char *param, size_t size)
{
    FILE* fp = fopen("a1.param", "r");
    if (!fp) pbc_die("error opening param file");
    size_t count = fread(param, 1, size, fp);
    if (!count) pbc_die("input error");
    fclose(fp);
    return count;
}

void getRand(mpz_t rand_number)
{
    char number[BYTESNUM];
    FILE* urandom = fopen("/dev/urandom", "r");
    fread(number, BYTESNUM, 1, urandom);    //read 128 bytes in /dev/urandom
    fclose(urandom);
    //printf ("\n number1024 : %s \n", number);
    mpz_import(rand_number, BYTESNUM, 1, sizeof(number[0]), 0, 0, number);
}

void getRandGtP(mpz_t nb, mpz_t p)
{
    getRand(nb);
    //gmp_printf ("\norderEC is random: %Zd\n", orderEC);
    while (mpz_cmp(nb, p) <= 0)
    {
        //  gmp_printf("\nnew nb is %Zd\n", nb);
        //  gmp_printf("\np is %Zd\n", p);
        //  printf ("\nmpz_cmp %d\n", mpz_cmp(p, nb));
        getRand(nb);
        //return;
    }
}

void verifalloc(uintptr_t *w)
{
    if(w == NULL){
    fprintf(stderr,"Memory allocation failed \n");
    exit(1);
    }
    else
    {
        #ifdef DEBUG_TRACING
        printf("Memory allocation success \n");
        #endif
    }
}
