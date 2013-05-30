#include <pbc/pbc.h>
#include <pbc/pbc_test.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

//BYTESNUM is the size of bytes we want to read in /dev/urandom
#define BYTESNUM 128

//generate number to 2n-1
void pbc_mpz_urandomb(mpz_t z, unsigned int bits);

//readConfig will read the pairing parameter in a1.param
size_t readConfig(char *param, size_t size);

//function to generate random number from /dev/urandom
void getRand(mpz_t rand_number);

//function that verifies that rand number <= p(order of EC)
void getRandGtP(mpz_t nb, mpz_t p);

//funcion that verifies the allocation
void verifalloc(uintptr_t w);

