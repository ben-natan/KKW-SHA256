#include <stdio.h>
#include <memory.h>
#include <limits.h>
#include <assert.h>
#include "sha256.h"
#include "picnic3_impl.h"

#define WORD_SIZE_BITS 32


int projet_sign(unsigned char witness[8])
{
    int numWitBytes = 8;
    int numWitBits = 8*numWitBytes;

    unsigned char publicHash[64];  //512 bits


    printf("SHA");
    fflush(stdout);

    sha256(publicHash, witness, numWitBits);

    printHex("publicHash", (uint8_t*)publicHash, 512);

    // paramset_t* params = malloc(60);
    paramset_t* params = (paramset_t*)malloc(sizeof(paramset_t));
    params->stateSizeBits = 32;
    params->numMPCRounds = 3;
    params->numOpenedRounds = 2;
    params->numMPCParties = 16;
    params->digestSizeBytes = 32;

    params->andSizeBytes = 5312; // d'après calcul sur feuille 
    params->stateSizeBytes = 4;
    params->seedSizeBytes = 1;
    params->stateSizeWords = (params->stateSizeBits + WORD_SIZE_BITS - 1)/ WORD_SIZE_BITS;
    params->transform = 255;
    params->saltSizeBytes = 32; /* same for all parameter sets */


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

    printf("Signature");
    fflush(stdout);

    int ret = sign_picnic3((uint32_t*)witness, (uint32_t*)publicHash, sig, params);
    return ret;
}