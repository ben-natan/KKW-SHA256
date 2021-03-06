/*! @file picnic3_impl.h
 *  @brief This is the main implementation file of the signature scheme for
 *  the Picnic3 parameter sets.
 *
 *  This file is part of the reference implementation of the Picnic signature scheme.
 *  See the accompanying documentation for complete details.
 *
 *  The code is provided under the MIT license, see LICENSE for
 *  more details.
 *  SPDX-License-Identifier: MIT
 */

#ifndef PICNIC3_IMPL_H
#define PICNIC3_IMPL_H

#include <stdint.h>
#include <stddef.h>

typedef enum {
    TRANSFORM_FS = 0,
    TRANSFORM_UR = 1,
    TRANSFORM_INVALID = 255
} transform_t;

// typedef struct paramset_SHA256_t {
//     uint32_t numRounds;
//     uint32_t numSboxes;
//     uint32_t stateSizeBits;
//     uint32_t stateSizeBytes;
//     uint32_t stateSizeWords;
//     uint32_t andSizeBytes;
//     uint32_t UnruhGWithoutInputBytes;
//     uint32_t UnruhGWithInputBytes;
//     uint32_t numMPCRounds;          // T
//     uint32_t numOpenedRounds;       // u
//     uint32_t numMPCParties;         // N
//     uint32_t seedSizeBytes;
//     uint32_t saltSizeBytes;
//     uint32_t digestSizeBytes;
//     transform_t transform;
// } paramset_SHA256_t;



typedef struct paramset_SHA256_t {
    uint32_t stateSizeBits;
    uint32_t stateSizeBytes;
    uint32_t stateSizeWords;
    uint32_t inputSizeBits;
    uint32_t wordSizeBits;
    uint32_t andSizeBytes;
    uint32_t andSizeBits;
    uint32_t UnruhGWithoutInputBytes;
    uint32_t UnruhGWithInputBytes;
    uint32_t numMPCRounds;          // T
    uint32_t numOpenedRounds;       // u
    uint32_t numMPCParties;         // N
    uint32_t seedSizeBytes;
    uint32_t saltSizeBytes;
    uint32_t digestSizeBytes;
    transform_t transform;
} paramset_SHA256_t;

typedef struct proof2_t {
    uint8_t* seedInfo;          // Information required to compute the tree with seeds of of all opened parties
    size_t seedInfoLen;         // Length of seedInfo buffer
    uint8_t* aux;               // Last party's correction bits; NULL if P[t] == N-1
    uint8_t* C;                 // Commitment to preprocessing step of unopened party
    uint8_t* input;             // Masked input used in online execution
    uint8_t* msgs;              // Broadcast messages of unopened party P[t]
} proof2_t;

typedef struct signature2_t {
    uint8_t* salt;
    uint8_t* iSeedInfo;         // Info required to recompute the tree of all initial seeds
    size_t iSeedInfoLen;
    uint8_t* cvInfo;            // Info required to check commitments to views (reconstruct Merkle tree)
    size_t cvInfoLen;
    uint8_t* challengeHash;
    uint16_t* challengeC;
    uint16_t* challengeP;
    proof2_t* proofs;           // One proof for each online execution the verifier checks
} signature2_t;

int sign_picnic3(uint32_t* witness, uint32_t* publicHash, signature2_t* sig, paramset_SHA256_t* params);
int verify_picnic3(signature2_t* sig, const uint32_t* publicHash, paramset_SHA256_t* params);

void allocateSignature2(signature2_t* sig, paramset_SHA256_t* params);
void freeSignature2(signature2_t* sig, paramset_SHA256_t* params);

/* Returns the number of bytes written on success, or -1 on error */
int serializeSignature2(const signature2_t* sig, uint8_t* sigBytes, size_t sigBytesLen, paramset_SHA256_t* params);
/* Returns EXIT_SUCCESS on success or EXIT_FAILURE on error */
int deserializeSignature2(signature2_t* sig, const uint8_t* sigBytes, size_t sigBytesLen, paramset_SHA256_t* params);

uint8_t getBit(const uint8_t* array, uint32_t bitNumber);

uint32_t ceil_log2(uint32_t x);
void printHex(const char* s, const uint8_t* data, size_t len);

#endif /* PICNIC3_IMPL_H */
