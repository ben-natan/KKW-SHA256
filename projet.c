#include <stdio.h>
#include <memory.h>
#include <limits.h>
#include <assert.h>
#include "sha256.h"
#include "picnic3_impl.h"
#include <time.h>

#define WORD_SIZE_BITS 32


int projet_sign_and_verify(uint32_t* witness)
{
    int numWitBytes = 8;
    int numWitBits = 8*numWitBytes;

    unsigned char publicHash[32];  //256 bits

    sha256(publicHash, numWitBits);

    // printHex("publicHash", (uint8_t*)publicHash, 32);

    // paramset_t* params = malloc(60);
    paramset_SHA256_t* params = (paramset_SHA256_t*)malloc(sizeof(paramset_SHA256_t));
    params->stateSizeBits = 83 * 32;
    params->numMPCRounds = 352;  // M 352
    params->numOpenedRounds = 33;  // Tau 33
    params->numMPCParties = 16;
    params->digestSizeBytes = 64;  // pour rho = 128
    params->andSizeBytes = 5824; 
    params->stateSizeBytes = 4;
    params->seedSizeBytes = 2;  // pour rho = 128 : numBytes(2 * 128)
    params->stateSizeWords = (params->stateSizeBits + WORD_SIZE_BITS - 1)/ WORD_SIZE_BITS;
    params->transform = 255;
    params->saltSizeBytes = 32; /* same for all parameter sets */
    params->inputSizeBits = 512;
    params->wordSizeBits = 32;
    params->andSizeBits = 46592;   // nombre de and gates


    signature2_t* sig = (signature2_t*)malloc(sizeof(signature2_t));
    sig->salt = (uint8_t*)malloc(params->saltSizeBytes);
    sig->iSeedInfo = NULL;
    sig->iSeedInfoLen = 0;
    sig->cvInfo = NULL;       // Sign/verify code sets it
    sig->cvInfoLen = 0;
    sig->challengeC = (uint16_t*)malloc(params->numOpenedRounds * sizeof(uint16_t));
    sig->challengeP = (uint16_t*)malloc(params->numOpenedRounds * sizeof(uint16_t));
    sig->challengeHash = (uint8_t*)malloc(params->digestSizeBytes);
    sig->proofs = calloc(params->numMPCRounds, sizeof(proof2_t));




    double total_sign = 0;
    double total_ver = 0;
    
    int i, ret;
    for (i = 0; i < 10; i++) {
        clock_t begin_sign = clock();
        ret = sign_picnic3(witness, (uint32_t*)publicHash, sig, params);
        clock_t end_sign = clock();

        total_sign += (double)(end_sign - begin_sign) / CLOCKS_PER_SEC; 

        clock_t begin_ver = clock();
        ret = verify_picnic3(sig, (uint32_t*)publicHash, params);
        clock_t end_ver = clock();

        total_ver += (double)(end_ver - begin_ver) / CLOCKS_PER_SEC;

        uint8_t* sigBytes = malloc(500000);
        int size = serializeSignature2(sig, sigBytes, 500000, params);
        printf("Éxécution %d  -- %dKB\n", i, size/1000);
    }

    printf("Total sign: %f \n", total_sign);
    printf("Total ver: %f \n", total_ver);
    printf("Temps total: %f \n", total_sign + total_ver);

    return ret;
}