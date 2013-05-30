#include <pbc/pbc.h>
#include <pbc/pbc_test.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include "math.h"

#define PARAM_SIZE 1024
#define KEY_SIZE 1024
#define n 16
#define m 16

#define DEBUG_TRACING

//n is the total number of attribute
//m is the max value that an attribute can have
//PARAM_SIZE is the size of pairing param

// Declaration of functions
void setup();


int main()
{
    printf("***********************************************************************************\n");
    printf("***********************************************************************************\n");
    printf("***********************************************************************************\n");
    printf("******************ABBE Scheme Allowing Arbitrary Access Policies*******************\n");
    printf("*******************Created by Pascal Junod and Alexandre Karlov********************\n");
    printf("*************************Implemented by Cedric De Carvalho*************************\n");
    printf("**************All rights reserved by HEIG-VD and Kudelski Nagravision**************\n");
    printf("***********************************************************************************\n");
    printf("***********************************************************************************\n");
    printf("***********************************************************************************\n");
    printf("***********************************************************************************\n");

    setup();

    return 0;
}

void setup()
{
    //VARIABLES INITIALIZATION
    pairing_t         pairing;              //decla of pairing
    //unsigned long     k       = 2;        //nb of attributes in this exampl(A1 + A2) & (A3 + A4)
    unsigned long     a1      = 1;          //attribute 1
    unsigned long     a2      = 2;          //attribute 2
    unsigned long     a3      = 3;          //attribute 3
    unsigned long     a4      = 4;          //attribute 4
    unsigned long     N1       = n;         //nb of positives attributes
    unsigned long     N2       = n;         //nb of negatives attributes
    unsigned long     l       = 10000000;   //nb of users
    unsigned long     nbclause       = 2;   //nb of clauses
    unsigned long j;                        //for loop using unsigned long
    int i;                                  //for loop using int

    //unsigned long   random_number     = NULL;
    size_t            count;
    char              param[PARAM_SIZE];
    //    FILE* attr = fopen("attributes.txt", "r");
    //    if (!attr) pbc_die("error opening attributes file");
    //    read_attr(attr);

    //Declarations of PBC's elements

    element_t         g         ;       //g is a random generator of G
    element_t         sessionkey;       //the global session key for CNF
    element_t         ggamma;           //g^gamma
    element_t         galpha;           //g^alpha
    element_t         gbeta;            //g^beta
    element_t         gsu;              //g^su
    element_t         gair;             //v^r
    element_t         gn;               //g^n
    element_t         resultdkele;      //g(1)^(r*(beta + su))
    element_t         resultgti;        //g^t[i]
    element_t         decrypta;         //dividende of decrypt header division
    element_t         decryptb;         //diviser of decrypt header division
    element_t         decryptc;         //add of all session key
    element_t         decryptc1;        //1st header session key
    element_t         decryptc2;        //2nd header key
    element_t         decryptd;         //global
    element_t         decrypte;         //global session key decrypted
    element_t         hdr0;             //g(n) ^ t
    element_t         sum_gnsu;         //t (sum of all t[i]
    element_t         tempsession;      //used during session's calculation

    //Declarations of gmp numbers

    mpz_t             alpha;                //random number Z/Zp
    mpz_t             gamma;                //random number Z/Zp
    mpz_t             beta;                 //random number Z/Zp
    mpz_t             air;                  //random number Z/Zp
    mpz_t             orderEC;               //order of Elliptics Curves
    mpz_t             su;                   //random number Z/Zp
    mpz_t             resultalphaair;       //alpha * r, used for public keys
    mpz_t             resgbeta;             //g^beta
    mpz_t             resultsu;             //alpha * su
    mpz_t             resultdk1tmp;         //for calculate resultdkele
    mpz_t             betasu;               //beta + su
    mpz_t             gammasu;              //gamma * su
    mpz_t             sum_t;                //sum of t[i]
    mpz_t             alphan;               //alpha ^ n
    mpz_t             hdr0tmp;              //for calculate hdr0

    char comparo[] = "36203638728584889925158415861634051131656232976339194924022065306723188923966451762160327870969638730567198058600508960697138006366861790409776528385407283664860565239295291314844246909284597617282274074224254733917313218308080644731349763985110821627195514711746037056425804819692632040479575042834043863089";

    //Initialization of gmp numbers
    mpz_init(orderEC);
    mpz_set_str(orderEC, comparo, 10);
    mpz_init(alpha);
    mpz_init(gamma);
    mpz_init(beta);
    mpz_init(air);
    mpz_init(su);
    mpz_init(resultalphaair);
    mpz_init(resgbeta);
    mpz_init(resultsu);
    mpz_init(resultdk1tmp);
    mpz_init(betasu);
    mpz_init(gammasu);
    mpz_init(sum_t);
    mpz_init(alphan);
    mpz_init(hdr0tmp);

    //generate random value Z/pZ
    getRandGtP(alpha,orderEC);
    getRandGtP(gamma,orderEC);
    getRandGtP(beta,orderEC);
    getRandGtP(air,orderEC);
    getRandGtP(su,orderEC);

    #ifdef DEBUG_TRACING

    printf("number of attributes : %i\n", n);
    printf("number of users : %lu\n", l);

    gmp_printf ("\nalpha is random: %Zd\n", alpha);
    gmp_printf ("\ngamma is random: %Zd\n", gamma);
    gmp_printf ("\nbeta is random: %Zd\n", beta);
    gmp_printf ("\nair is random: %Zd\n", air);
    gmp_printf ("\nsu is random: %Zd\n", su);
    gmp_printf ("\norderEC is from a1.param: %Zd\n", orderEC);

    #endif
    // CODE
    //open the file that contain the param n,p and l then set them in param
    count = readConfig(param, PARAM_SIZE);
    if(pairing_init_set_buf(pairing, param, count))
        pbc_die("pairing error");

    //initialization of tables
    int ek_size = (n * 2) + 2;              //number of public keys
    int dk_size = (n * 2) + N1 + N2;        //number of private keys
    int h1_size = nbclause;                 //number of CNF header C0
    int h2_size = nbclause;                 //number of DNF header C1
    int t_size = nbclause;                  //number of t[i]
    int tj_size = m;                        //number of t[i]
    #ifdef DEBUG_TRACING
    printf("\n number of attributes = %i \n", n);
    printf("\n number of privates keys = %i \n", ek_size);
    printf("\n number of publics keys = %i \n", dk_size);
    printf("\n number of clauses = %i \n", t_size);
    #endif

    //allocate memory
    uintptr_t *ek = malloc(ek_size * sizeof(element_t));        //public keys
    uintptr_t *dk = malloc(dk_size * sizeof(element_t));        //private keys
    uintptr_t *head1st = malloc(h1_size * sizeof(element_t));   //C0
    uintptr_t *t = malloc(t_size * sizeof(mpz_t));              //t[i]
    uintptr_t *head2nd = malloc(h2_size * sizeof(element_t));   //C1
    //uintptr_t *tj = malloc(t_size * sizeof(mpz_t));
    verifalloc(ek);
    verifalloc(dk);
    verifalloc(head1st);
    verifalloc(t);
    verifalloc(head2nd);
    //verifalloc(tj);

    //loop for t[i] memory allocation and calculate t
    for(i=1; i <= t_size; i++)
    {
        t[i] = (uintptr_t)malloc(sizeof(mpz_t));
        // mpz_t temp;
        // *temp = (mpz_t)t[i];
        //mpz_init(temp);
        mpz_init(t[i]);
        getRandGtP(t[i], orderEC);
        #ifdef DEBUG_TRACING
        gmp_printf("\n\n tN[%d]: %Zd\n\n",i,t[i]);
        #endif
        mpz_add(sum_t,sum_t,t[i]);
        mpz_mod(sum_t,sum_t,orderEC);
        verifalloc(t[i]);
    }
    //loop for public keys memory allocation
    for(i=0; i < ek_size; i++)
    {
        ek[i] = (uintptr_t)malloc(sizeof(element_t));
        element_init_G1(ek[i], pairing);
        verifalloc(ek[i]);
    }
    //loop for private keys memory allocation
    for(i=0; i < dk_size; i++)
    {
        dk[i] = malloc(sizeof(element_t));
        element_init_G1(dk[i], pairing);
        verifalloc(dk[i]);
    }
    //loop for C0 of header : g^(r*ti) memory allocation
    for(i=1; i <= h1_size; i++)
    {
        head1st[i] = malloc(sizeof(element_t));
        element_init_G1(head1st[i], pairing);
        verifalloc(head1st[i]);
    }

    // initialization of pairing's elements

    //input pairing parameters
    element_init_G1(g, pairing);                    //random generator of G
    element_init_G1(resultdkele, pairing);          //res of g(1)^(r*(beta + su))
    element_init_G1(ggamma, pairing);               //res of g^gamma
    element_init_G1(gsu, pairing);                  //res of g^su
    element_init_G1(galpha, pairing);               //res of g^alpha
    element_init_G1(gair, pairing);                 //res of v^r
    element_init_G1(gbeta, pairing);                //res of g^beta
    element_init_G1(gn, pairing);                   //res of g^n
    element_init_G1(resultgti, pairing);            //res of g^t[i]
    element_init_G1(sum_gnsu, pairing);             //res of t which is the sum of t[i]
    element_init_G1(hdr0, pairing);                 //res of c0 which is g(n) ^ t

    //output pairing parameters
    element_init_GT(sessionkey, pairing);           //session key, given by e(g(1)^r,g(n)^beta)^t
    element_init_G1(tempsession, pairing);          //res of mul(dk * sum g(n+1-j+k)^su)
    element_init_GT(decrypta, pairing);
    element_init_GT(decryptb, pairing);
    element_init_GT(decryptc, pairing);
    element_init_GT(decryptc1, pairing);
    element_init_GT(decryptc2, pairing);
    element_init_GT(decryptd, pairing);
    element_init_GT(decrypte, pairing);

    //verifying that G1 = G2
    if (!pairing_is_symmetric(pairing))
    {
        fprintf(stderr, "only works with symmetric pairing\n");
        exit(1);
    }


    //{int line = __LINE__; printf("\n%d\n", line);}

    //generate system parameters

    //generate g a random element in G
    element_random(g);


    //calculate g^gamma
    element_pow_mpz(ggamma, g, gamma);

    //calculate alpha^n
    mpz_powm_ui(alphan, alpha, n,orderEC);

    //calculate v^r
    element_pow_mpz(gair, ggamma, air);

    //calculate g(n)^b
    mpz_mul (resgbeta, beta, alphan);
    mpz_mod(resgbeta,resgbeta,orderEC);
    element_pow_mpz(gbeta, g, resgbeta);

    //calculate g(n)^r(beta+su)
    mpz_add(betasu,beta,su);
    mpz_mod(betasu,betasu,orderEC);
    mpz_mul(resultdk1tmp, betasu, air);
    mpz_mul(resultdk1tmp, resultdk1tmp, alpha);
    mpz_mod(resultdk1tmp,resultdk1tmp,orderEC);
    element_pow_mpz(resultdkele, g, resultdk1tmp);

    #ifdef DEBUG_TRACING
    element_printf("\n\ndk[0]: %B\n\n",resultdkele);
    element_printf("\n\ng is a random generator of EC: %B\n\n",g);
    element_printf("\n\ng^gamma: %B\n\n",ggamma);
    element_printf("\n\nv^r: %B\n\n",gair);
    element_printf("\n\ng(n)powbeta: %B\n\n",gbeta);
    #endif

    //calculate gamma * su
    mpz_mul(gammasu,gamma,su);
    mpz_mod(gammasu,gammasu,orderEC);

    int indiceek=0;
    int indicedk=0;

    //********************************calculate publics keys*****************************//
    // ek[0]n=1 to ek[15]n=16
    // g(1)^r to g(n)^r
    for(j=1; j <= n; j++)
    {
        mpz_t temp;
        mpz_init(temp);
        mpz_powm_ui(temp, alpha, j, orderEC);
        mpz_mul (resultalphaair, temp, air);
        mpz_mod(resultalphaair,resultalphaair,orderEC);
        element_pow_mpz(ek[indiceek++],g,resultalphaair);
        printf ("\nek number to n: %hu \n", indiceek);
    }
    // ek[16]n=18 to ek[30]n=32
    //g(n+2)^r to g(2n)^r
    for(j=n+2; j <= 2*n; j++)
    {
        mpz_t temp;
        mpz_init(temp);
        mpz_powm_ui(temp, alpha, j, orderEC);
        mpz_mul (resultalphaair, temp, air);
        mpz_mod(resultalphaair,resultalphaair,orderEC);
        element_pow_mpz(ek[indiceek++],g,resultalphaair);
        printf ("\n number from n+2 to 2*n: %hu \n", indiceek);
    }
    ek[indiceek++] = gair; // ek[31] v^r
    ek[indiceek++] = gbeta; // ek[32] g(n)^b
    element_pow_mpz (ek[indiceek++], g, alphan ); // ek[33] g(n)

    #ifdef DEBUG_TRACING
    for(i=0; i < ek_size; i++)
    {
        element_printf("\n\n private key ek[%d]: %B\n\n",i,ek[i]);
    }
    #endif

    //**************************calculate privates keys*******************************//

    //dk[0]
    dk[indicedk++] = resultdkele; // g^(r(beta + su))
    //dk[1]n=1 to dk[16]n=16
    //g(1)^su to g(n)^su
    for(j=1; j <= n; j++)
    {
        mpz_t temp;
        mpz_init(temp);
        mpz_powm_ui(temp, alpha, j, orderEC);
        mpz_mul (resultsu, temp, su);
        mpz_mod(resultsu,resultsu,orderEC);
        #ifdef DEBUG_TRACING
        printf ("\n dk number of 1 to n: %hu \n", indicedk);
        #endif
        element_pow_mpz(dk[indicedk++],g,resultsu);

    }
    //dk[17]n=18 to dk[31]n=32
    //g(n+2)^su to g(2n)^su
    for(j=n+2; j <= 2*n; j++)

    {
        mpz_t temp;
        mpz_init(temp);
        mpz_powm_ui(temp, alpha, j, orderEC);
        mpz_mul (resultsu, temp, su);
        mpz_mod(resultsu,resultsu,orderEC);
        #ifdef DEBUG_TRACING
        printf ("\n dk number of n+2 to 2*n: %hu \n", indicedk);
        #endif
        element_pow_mpz(dk[indicedk++],g,resultsu);
    }
    //dk[32]N1=1 to dk[47]N1=16
    //di1 to diN1
    for(j=1; j <= N1; j++)
    {
        mpz_t temp;
        mpz_init(temp);
        mpz_powm_ui(temp, alpha, j, orderEC);
        mpz_mul (resultsu, temp, gammasu);
        mpz_mod(resultsu,resultsu,orderEC);
        #ifdef DEBUG_TRACING
        printf ("\n number of N1: %hu \n", indicedk);
        #endif
        element_pow_mpz(dk[indicedk++],g,resultsu);  //g^((gamma * su) * alpha^N1)
    }
    //dk[48]N2=1 to dk[63]N2=16
    //dj1 to djN2
    for(j=1; j <= N2; j++)
    {
        mpz_t temp;
        mpz_init(temp);
        mpz_powm_ui(temp, alpha, j, orderEC);
        mpz_mul(resultsu, temp, gammasu);
        mpz_mod(resultsu,resultsu,orderEC);
        #ifdef DEBUG_TRACING
        printf ("\n number of N2: %hu \n", indicedk);
        #endif
        element_pow_mpz(dk[indicedk++],g,resultsu);  //g^((gamma * su) * alpha^N2)
    }

    #ifdef DEBUG_TRACING
    for(i=0; i < dk_size - 1; i++)
    {
        element_printf("\n\n public key dk[%d]: %B\n\n",i,dk[i]);
    }
    element_printf("\n\n public key dk[63]: %B\n\n",dk[63]);
    #endif


    //**************************calculate Header***************************//
    int indicegti=1;

    // CNF //

    //Header 1st element
    for(j=1; j <= nbclause; j++)
    {
        mpz_t temp;
        mpz_init(temp);
        mpz_mul (temp, air, t[j]);
        mpz_mod(temp,temp,orderEC);
        element_pow_mpz(head1st[indicegti++],g,temp);   //g^(r*t[i]))

        //Header 2nd element - formula to compute the N part
        signed long int onez = 1;
        element_t temp3;
        head2nd[j] = malloc(sizeof(element_t));     //allocate memory for C1
        verifalloc(head2nd[i]);
        element_init_G1(temp3, pairing);
        element_init_G1(head2nd[j], pairing);
        if (j==1){
        element_add(temp3, ek[n+1-a1-1], ek[n+1-a2-1]);} //addition the rights points for 1st clause
        if (j==2){
        element_add(temp3, ek[n+1-a3-1], ek[n+1-a4-1]);} //addition the rights points for 2nd clause
        element_mul_si(head2nd[j],temp3,onez);      //head2nd = temp3 (onez is just a value=1)
        element_mul(head2nd[j],head2nd[j],gair);
        element_pow_mpz(head2nd[j],head2nd[j],t[j]);
    }
    #ifdef DEBUG_TRACING
    for(i=1; i <= h1_size; i++)
    {
        element_printf("\n\n header 1st ele[%d]: %B\n\n",i,head1st[i]);
    }

    for(i=1; i <= h2_size; i++)
    {
        element_printf("\n\n header 2st ele[%d]: %B\n\n",i,head2nd[i]);
    }
    #endif
    // DNF //
    /*
    for(unsigned long i=1; i <= nbclause; i++){
        mpz_t temp;
        mpz_init(temp);
        mpz_mul (temp, air, t[i]);
        mpz_mod_ui(temp,temp,orderEC);
        element_pow_mpz(rti[indicegti++],g,temp);

        //Header 2nd element - formula to compute the N part

        unsigned long one = 1;
        signed long two;
        head2nd[i] = malloc(sizeof(element_t));
        element_init_G1(head2nd[i], pairing);
        mpz_t temp6;
        mpz_init(temp6);
        mpz_add_ui (temp6, temp6, one);
        element_mul_mpz(head2nd[i],ek[n + 1 - i],temp6);
        element_mul(head2nd[i],head2nd[i],gair);
        element_pow_mpz(head2nd[i],head2nd[i],t[i]);
    }
    for(int i=0; i < t_size; i++){
        element_printf("\n\n header 1st ele[%d]: %B\n\n",i,rti[i]);
    }
    for(int i=1; i <= h_size; i++){
        element_printf("\n\n header 2st ele[%d]: %B\n\n",i,head2nd[i]);
    }
    */

    pairing_apply(sessionkey,ek[0],ek[32],pairing);         //pairing for global session key
    element_pow_mpz(sessionkey,sessionkey,sum_t);           //the pairing has to be ^t
    element_printf("\n\nthe session key is: \n%B\n\n",sessionkey);

    //**************************Decrypt***************************//

    //**************************CNF*******************************//

    for(j=1; j <= nbclause; j++)
    {
        //for each clause, calculate the temp session key associated
        //clause 1
        if(j==1)
        {
        pairing_apply(decrypta,dk[a1],head2nd[j],pairing);      //pairing dividende
        element_add(tempsession,dk[a1+31],dk[n+1-a2+a1]);
        pairing_apply(decryptb,tempsession,head1st[j],pairing); //pairing diviser
        element_div(decryptc1,decrypta,decryptb);               //temp session key
        }
        //clause 2
        if(j==2)
        {
        pairing_apply(decrypta,dk[a3],head2nd[j],pairing);      //temp session key
        element_add(tempsession,dk[a3+31],dk[n+1-a4+a3]);
        pairing_apply(decryptb,tempsession,head1st[j],pairing);
        element_div(decryptc2,decrypta,decryptb);
        }
    }
    element_add(decryptc,decryptc1,decryptc2);  //all temps sessions keys add
    mpz_mul(hdr0tmp,sum_t,alphan);              //
    mpz_mod(hdr0tmp,hdr0tmp,orderEC);
    element_pow_mpz(hdr0,g,hdr0tmp);            //hdr0, g^(r*t[i])
    pairing_apply(decryptd,hdr0,dk[0],pairing); //pairing dividende of global session
    element_div(decrypte,decryptd,decryptc);    //calculate the global session key decrypted
    element_printf("\n\nthe session key finded by decrypt is: \n%B\n\n",decrypte);
     //**************************DNF*******************************//

    /*
    for(unsigned int j=1; j <= nbclause; j++)
        {
            if (j==1){
            pairing_apply(decrypta,dk[a1],head2nd[j],pairing);
            element_mul(tempsession,dk[a1+31],dk[n+1-a2+a1]);
            pairing_apply(decryptb,tempsession,head1st[j],pairing);
            element_div(decryptc1,decrypta,decryptb);
            }
            if (j==2){
            pairing_apply(decrypta,dk[a3],head2nd[j],pairing);
            element_mul(tempsession,dk[a3+31],dk[n+1-a4+a3]);
            pairing_apply(decryptb,tempsession,head1st[j],pairing);
            element_div(decryptc2,decrypta,decryptb);
            }
        }
    element_add(decryptc,decryptc1,decryptc2);
    mpz_mul(hdr0tmp,sum_t,alphan);
    mpz_mod(hdr0tmp,hdr0tmp,orderEC);
    element_pow_mpz(hdr0,g,hdr0tmp);
    pairing_apply(decryptd,hdr0,dk[0],pairing);
    element_div(decrypte,decryptd,decryptc);
    element_printf("\n\nthe session key finded by decrypt is: \n%B\n\n",decrypte);
    */

    //compare the global session key with the decrypted global session key
    if(!element_cmp(sessionkey, decrypte))
    {
        printf("CNF Session key has been decrypted\n");
    }
    else
    {
        printf("CNF Session key hasn't been decrypted\n");
    }

    //free allocated
    free(ek);
    free(dk);
    free(head1st);
    free(head2nd);
    free(t);

    //clear all elements
    element_clear(g);
    element_clear(ggamma);
    element_clear(galpha);
    element_clear(gair);
    element_clear(gbeta);
    element_clear(resultgti);
    element_clear(gn);
    element_clear(sessionkey);
    element_clear(decrypta);
    element_clear(decryptb);
    element_clear(decryptc);
    element_clear(decryptc1);
    element_clear(decryptc2);
    element_clear(decryptd);
    element_clear(decrypte);
    element_clear(hdr0);
    element_clear(tempsession);
   // element_clear(temp3);
    pairing_clear(pairing);
}

