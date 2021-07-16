/*! @file picnic3_impl.c
 *  @brief This is the main file of the signature scheme for the Picnic3
 *  parameter sets.
 *
 *  This file is part of the reference implementation of the Picnic signature scheme.
 *  See the accompanying documentation for complete details.
 *
 *  The code is provided under the MIT license, see LICENSE for
 *  more details.
 *  SPDX-License-Identifier: MIT
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "picnic3_impl.h"
#include "picnic_types.h"
#include "hash.h"
#include "tree.h"

#define MIN(a,b)            (((a) < (b)) ? (a) : (b))

// #define MAX_AUX_BYTES ((LOWMC_MAX_AND_GATES + LOWMC_MAX_KEY_BITS) / 8 + 1)
#define MAX_AUX_BYTES 93696 

#define GETBIT(x, i) (((x) >> (i)) & 0x01)
#define SETBIT(x, i, b)   x= (b)&1 ? (x)|(1 << (i)) : (x)&(~(1 << (i)))
#define RIGHTROTATE(x,n) (((x) >> (n)) | ((x) << (32-(n))))


/* Get one bit from a byte array */
uint8_t getBit(const uint8_t* array, uint32_t bitNumber)
{
    return (array[bitNumber / 8] >> (7 - (bitNumber % 8))) & 0x01;
}

/* Get one bit from a 32-bit int array */
uint8_t getBitFromWordArray(const uint32_t* array, uint32_t bitNumber)
{
    return getBit((uint8_t*)array, bitNumber);
}

/* Set a specific bit in a byte array to a given value */
void setBit(uint8_t* bytes, uint32_t bitNumber, uint8_t val)
{
    bytes[bitNumber / 8] = (bytes[bitNumber >> 3]
                            & ~(1 << (7 - (bitNumber % 8)))) | (val << (7 - (bitNumber % 8)));
}

/* Set a specific bit in a byte array to a given value */
void setBitInWordArray(uint32_t* array, uint32_t bitNumber, uint8_t val)
{
    setBit((uint8_t*)array, bitNumber, val);
}

uint32_t numBytes(uint32_t numBits)
{
    return (numBits == 0) ? 0 : ((numBits - 1) / 8 + 1);
}

void xor_array(uint32_t* out, const uint32_t * in1, const uint32_t * in2, uint32_t length)
{
    for (uint32_t i = 0; i < length; i++) {
        out[i] = in1[i] ^ in2[i];
    }
}

int arePaddingBitsZero(uint8_t* data, size_t bitLength)
{
    size_t byteLength = numBytes(bitLength); 
    for (size_t i = bitLength; i < byteLength * 8; i++) {
        uint8_t bit_i = getBit(data, i);
        if (bit_i != 0) {
            return 0;
        }
    }
    return 1;
}

void printMsgs(uint8_t* msgs)
{
    for (int i = 0; i < 64; i++) {
        uint8_t bit = getBit(msgs, i);
        printf("%d", bit);
    }
}

void printHex(const char* s, const uint8_t* data, size_t len)
{
    printf("%s: ", s);
    for (size_t i = 0; i < len; i++) {
        printf("%02X", data[i]);
    }
    printf("\n");
}

void printInputMasks(shares_t* input_masks)
{
    for (size_t i = 0; i < input_masks->numWords; i++) {
        printf("%d ", input_masks->shares[i]);
    }
}

// Odd or even number of 1 bits in x (of size 16 bits)
static uint16_t parity16(uint16_t x)
{
    uint16_t y = x ^ (x >> 1);

    y ^= (y >> 2);
    y ^= (y >> 4);
    y ^= (y >> 8);
    return y & 1;
}


static void setBitSO(uint32_t* output, int p, uint8_t bit)
{
    if (bit == 1) {
        output[0] |= 1UL << p;
    } else {
        output[0] &= ~(1UL << p);
    }
}


static void reconstructWordMask3(uint32_t* output, shares_t* shares, int p)
{
    for (size_t i = 0; i < 32; i++) {
        setBitSO(output, 31 - i, (uint8_t)parity16(shares->shares[32 * p + i]));
    }
}

uint16_t getMask(int p, int i, shares_t* state_masks) 
{
    return state_masks->shares[32*p + i];
}


static void getMasks(int p, uint16_t* masks, shares_t* state_masks)
{
    for (int i = 0; i < 32; i++) {
        masks[i] = state_masks->shares[32*p + i];
    }
}


static void setMask(int p, int i, uint16_t mask, shares_t* state_masks)
{
    state_masks->shares[32*p + i] = mask;
}

static void loadInputMasks(shares_t* state_masks, shares_t* input_masks)
{
    for (int p = 0; p < 16; p++) {
        for (int i = 0; i < 32; i++) {
            state_masks->shares[32*p + i] = input_masks->shares[32*p + i];
        }
    }

    for (int p = 16; p < 83; p++) {
        for (int i = 0; i < 32; i++) {
            state_masks->shares[32*p + i] = 0;
        }
    }
}


// FONCTIONNE
static void loadS0Masks(int i, shares_t* mask_shares)
{
    int j;
    for (j = 0; j < 3; j++) {
        mask_shares->shares[64*32 + j] = mask_shares->shares[32*(i-14) - 7 + j]
                                    ^ mask_shares->shares[32*(i-14) - 18 + j];
    }
    for (j = 3; j < 7; j++) {
        mask_shares->shares[64*32 + j] = mask_shares->shares[32*(i-14) - 7 + j]
                                    ^ mask_shares->shares[32*(i-14) - 18 + j]
                                    ^ mask_shares->shares[32*(i-15) + j - 3];
    }
    for (j = 7; j < 18; j++) {
        mask_shares->shares[64*32 + j] = mask_shares->shares[32*(i-15) + j - 7]
                                    ^ mask_shares->shares[32*(i-14) - 18 + j]
                                    ^ mask_shares->shares[32*(i-15) + j - 3];
    }
    for (j = 18; j < 32; j++) {
        mask_shares->shares[64*32 + j] = mask_shares->shares[32*(i-15) + j - 7]
                                    ^ mask_shares->shares[32*(i-15) + j - 18]
                                    ^ mask_shares->shares[32*(i-15) + j - 3];
    }
}


static void loadS1Masks(int i, shares_t* mask_shares)
{
    int j; 
    for (j = 0; j < 10; j++) {
        mask_shares->shares[65*32 + j] = mask_shares->shares[32*(i-1) - 17 + j]
                                    ^ mask_shares->shares[32*(i-1) - 19 + j];
    }
    for (j = 10; j < 17; j++) {
        mask_shares->shares[65*32 + j] = mask_shares->shares[32*(i-1) - 17 + j]
                                    ^ mask_shares->shares[32*(i-1) - 19 + j]
                                    ^ mask_shares->shares[32*(i-2) + j - 10];
    }
    for (j = 17; j < 19; j++) {
        mask_shares->shares[65*32 + j] = mask_shares->shares[32*(i-2) + j - 17]
                                    ^ mask_shares->shares[32*(i-1) - 19 + j]
                                    ^ mask_shares->shares[32*(i-2) + j - 10];
    }
    for (j = 19; j < 32; j++) {
        mask_shares->shares[65*32 + j] = mask_shares->shares[32*(i-2) + j - 17]
                                    ^ mask_shares->shares[32*(i-2) + j - 19]
                                    ^ mask_shares->shares[32*(i-2) + j - 10];
    }
}

static void loadS1Masks2(shares_t* mask_shares)
{
    int j;
    uint16_t e_masks[32]; 
    getMasks(72, e_masks, mask_shares);
    for (j = 0; j < 6; j++) {
        mask_shares->shares[65*32 + j] = e_masks[32 - 6 + j]
                                        ^ e_masks[32 - 11 + j]
                                        ^ e_masks[32 - 25 + j];
    }
    for (j = 6; j < 11; j++) {
        mask_shares->shares[65*32 + j] = e_masks[j - 6]
                                        ^ e_masks[32 - 11 + j]
                                        ^ e_masks[32 - 25 + j];
    }
    for (j = 11; j < 25; j++) {
        mask_shares->shares[65*32 + j] = e_masks[j - 6]
                                        ^ e_masks[j - 11]
                                        ^ e_masks[32 - 25 + j];
    }
    for (j = 25; j < 32; j++) {
        mask_shares->shares[65*32 + j] = e_masks[j - 6]
                                        ^ e_masks[j - 11]
                                        ^ e_masks[j - 25];
    }
}


static void loadS0Masks2(shares_t* mask_shares)
{
    int j;
    uint16_t a_masks[32];
    getMasks(68, a_masks, mask_shares);
    for (j = 0; j < 2; j++) {
        mask_shares->shares[64*32 + j] = a_masks[32 - 2 + j]
                                        ^ a_masks[32 - 13 + j]
                                        ^ a_masks[32 - 22 + j];
    }
    for (j = 2; j < 13; j++) {
        mask_shares->shares[64*32 + j] = a_masks[j - 2]
                                        ^ a_masks[32 - 13 + j]
                                        ^ a_masks[32 - 22 + j];
    }
    for (j = 13; j < 22; j++) {
        mask_shares->shares[64*32 + j] = a_masks[j - 2]
                                        ^ a_masks[j - 13]
                                        ^ a_masks[32 - 22 + j];
    }
    for (j = 22; j < 32; j++) {
        mask_shares->shares[64*32 + j] = a_masks[j - 2]
                                        ^ a_masks[j - 13]
                                        ^ a_masks[j - 22];
    }
}





/* Number of leading zeroes of x.
 * From the book
 * H.S. Warren, *Hacker's Delight*, Pearson Education, 2003.
 * http://www.hackersdelight.org/hdcodetxt/nlz.c.txt
 */
static int32_t nlz(uint32_t x)
{
    uint32_t n;

    if (x == 0) return (32);
    n = 1;
    if((x >> 16) == 0) {n = n + 16; x = x << 16;}
    if((x >> 24) == 0) {n = n + 8;  x = x << 8;}
    if((x >> 28) == 0) {n = n + 4;  x = x << 4;}
    if((x >> 30) == 0) {n = n + 2;  x = x << 2;}
    n = n - (x >> 31);

    return n;
}

uint32_t ceil_log2(uint32_t x)
{
    if (x == 0) {
        return 0;
    }
    return 32 - nlz(x - 1);
}


static void createRandomTapes(randomTape_t* tapes, uint8_t** seeds, uint8_t* salt, size_t t, paramset_SHA256_t* params)
{
    HashInstance ctx;

    size_t tapeSizeBytes = getTapeSizeBytes(params); 

    allocateRandomTape(tapes, params);
    for (size_t i = 0; i < params->numMPCParties; i++) {
        HashInit(&ctx, params, HASH_PREFIX_NONE);
        HashUpdate(&ctx, seeds[i], params->seedSizeBytes);
        HashUpdate(&ctx, salt, params->saltSizeBytes);
        HashUpdateIntLE(&ctx, t);
        HashUpdateIntLE(&ctx, i);
        HashFinal(&ctx);
        HashSqueeze(&ctx, tapes->tape[i], tapeSizeBytes);
    }
}


// tapes->pos correspond à w; tapes->tape[i] correspond à w[i]
static uint16_t tapesToWord(randomTape_t* tapes)
{
    uint16_t shares;

    for (size_t i = 0; i < 16; i++) {
        uint8_t bit = getBit(tapes->tape[i], tapes->pos);
        setBit((uint8_t*)&shares, i, bit);
    }
    tapes->pos++;
    return shares;
}

/* Read one bit from each tape and assemble them into a word.  The tapes form a
 * z by N matrix, we'll transpose it, then the first "count" N-bit rows forms
 * an output word.  In the current implementation N is 16 so the words are
 * uint16_t. The return value must be freed with freeShares().
 */

//" Read n bits from each of the N tapes, packing the shares into tmp shares. "
static void tapesToWords(shares_t* shares, randomTape_t* tapes)
{
    for (size_t w = 0; w < shares->numWords; w++) {
        shares->shares[w] = tapesToWord(tapes);   // la w-ieme share prend (tapes->tapes[i] pour 0 <= i <= 15) avec tapes->pos
    }
}

// static void copyShares(shares_t* dst, shares_t* src)
// {
//     assert(dst->numWords == src->numWords);
//     memcpy(dst->shares, src->shares, dst->numWords * sizeof(dst->shares[0]));
// }

// static void tapesToParityBits(uint32_t* output, size_t outputBitLen, randomTape_t* tapes)
// {
//     for (size_t i = 0; i < outputBitLen; i++) {
//         setBitInWordArray(output, i, parity16(tapesToWord(tapes)));
//     }
// }


/* For an input bit b = 0 or 1, return the word of all b bits, i.e.,
 * extend(1) = 0xFFFFFFFFFFFFFFFF
 * extend(0) = 0x0000000000000000
 * Assumes inputs are always 0 or 1.  If this doesn't hold, add "& 1" to the
 * input.
 */
static uint16_t extend(uint8_t bit)
{
    return ~(bit - 1);
}


// static uint8_t aux_mpc_AND2(uint8_t mask_a, uint8_t mask_b, randomTape_t* tapes, paramset_SHA256_t* params)
// {

//     // for (int u = 0; u < 16; u++) {
//         // setBit(tapes->tape[u], tapes->pos, u);
//     // }

//     uint16_t fresh_output_mask = tapesToWord(tapes);

//     // for (int u = 0; u < 16; u++) {
//     //     setBit(tapes->tape[u], tapes->pos, 16-u);
//     // }

//     uint16_t and_helper = tapesToWord(tapes);

//     // if (tapes->pos > 511 && tapes->pos < 512 + 32 * 4) {
//     //         printf("[AUX222](%d) bit_a = %d  bit_b = %d\n\n", tapes->pos, mask_a, mask_b);
//     // }

//     setBit((uint8_t*)&and_helper, params->numMPCParties - 1, 0);
//     uint16_t aux_bit = (mask_a & mask_b) ^ parity16(and_helper);
//     size_t lastParty = params->numMPCParties - 1; // 15 
//     setBit(tapes->tape[lastParty], tapes-> pos - 1, (uint8_t)aux_bit);

//     if (tapes->pos > 511 && tapes->pos < 512 + 32*4) {
//         // printf("[AUX] pos: %d\n", tapes->pos);
//         tapes->pos = tapes->pos - 2;
//         uint16_t trueOutputMask = tapesToWord(tapes);
//         uint16_t trueAH = tapesToWord(tapes);
//         // if (tapes->pos == 536) {
//         //     printf("[VOILA] %d   --->  %d == %d \n", trueAH, parity16(trueAH), (mask_a & mask_b));
//         // }
//         printf("[AUX](%d) and_helper = %d\n", tapes->pos, trueAH);
//         printf("          output_mask = %d \n", trueOutputMask);
//         printf("          mask_a = %d   mask_b = %d\n", mask_a, mask_b);
//         assert(parity16(trueAH) == (mask_a & mask_b));
//     }
    
//     return fresh_output_mask;
// }

static uint16_t aux_mpc_AND2(uint16_t mask_a, uint16_t mask_b, randomTape_t* tapes, paramset_SHA256_t* params)
{

    uint16_t fresh_output_mask = tapesToWord(tapes);

    uint16_t and_helper = tapesToWord(tapes);

    setBit((uint8_t*)&and_helper, params->numMPCParties - 1, 0);
    uint16_t aux_bit = (parity16(mask_a) & parity16(mask_b)) ^ parity16(and_helper);
    size_t lastParty = params->numMPCParties - 1; // 15 

    setBit(tapes->tape[lastParty], tapes-> pos - 1, (uint8_t)aux_bit);
    
    return fresh_output_mask;
}

// void aux_CH_mpc(uint32_t e, uint32_t f, uint32_t g, uint32_t* ch, randomTape_t* tapes, paramset_SHA256_t* params)
// {   
//     uint8_t t0_bit, e_bit, f_bit, g_bit, out_bit;
//     for (int i = 0; i < 32; i++) {

//         uint8_t e_bit = GETBIT(e, i);
//         uint8_t f_bit = GETBIT(f, i);
//         uint8_t g_bit = GETBIT(g, i);

//         uint8_t t0_bit = f_bit ^ g_bit;
//         uint8_t et0_bit = aux_mpc_AND2(e_bit, t0_bit, tapes, params);

//         ch_bit = et0_bit ^ g_bit;
//         SETBIT(*ch, i, out_bit);
//     }
// }

static void aux_CH_mpc(int pe, int pf, int pg, int pch, shares_t* state_masks, randomTape_t* tapes, paramset_SHA256_t* params)
{
    for (int i = 0; i < 32; i++) {
        uint16_t mask_e = getMask(pe, 31 - i, state_masks);
        uint16_t mask_f = getMask(pf, 31 - i, state_masks);
        uint16_t mask_g = getMask(pg, 31 - i, state_masks);

        // if ( tapes->pos > 20991 && tapes->pos < 20992 + 32*4) {
            // printf("[AUX_CH](%d)", tapes->pos);
        // }
        

        uint16_t mask_t0 = mask_f ^ mask_g;
        uint16_t mask_et0 = aux_mpc_AND2(mask_e, mask_t0, tapes, params);

        // if ( tapes->pos > 20991 && tapes->pos < 20992 + 32*4) {
        //     printf("          mask_e = %d  mask_f = %d  mask_g = %d  mask_t0 = %d  mask_et0 = %d\n", mask_e, mask_f, mask_g, mask_t0, mask_et0);
        // }

        uint16_t mask_ch = mask_et0 ^ mask_g;
        setMask(pch, 31 - i, mask_ch, state_masks);
    }
}


// // maj = (a & (b ^ c)) ^ (b & c);
// void aux_MAJ_mpc(uint32_t a, uint32_t b, uint32_t c, uint32_t* out, randomTape_t* tapes, paramset_SHA256_t* params)
// {
//     uint8_t t0_bit, t1_bit, a_bit, b_bit, c_bit, out_bit;
//     for (int i = 0; i < 32; i++) {
//         a_bit = GETBIT(a, i);
//         b_bit = GETBIT(b, i);
//         c_bit = GETBIT(c, i);

//         t0_bit = a_bit ^ b_bit;
//         t1_bit = a_bit ^ c_bit; 
//         out_bit = aux_mpc_AND2(t0_bit, t1_bit, tapes, params);
//         out_bit = a_bit ^ out_bit;
//         SETBIT(*out, i, out_bit);
//     }
// }


// maj = [(a ^ b) & (a ^ c)] ^ a
static void aux_MAJ_mpc(int pa, int pb, int pc, int pmaj, shares_t* state_masks, randomTape_t* tapes, paramset_SHA256_t* params)
{
    for (int i = 0; i < 32; i++) {
        uint16_t mask_a = getMask(pa, 31 - i, state_masks);
        uint16_t mask_b = getMask(pb, 31 - i, state_masks);
        uint16_t mask_c = getMask(pc, 31 - i, state_masks);

        uint16_t mask_t0 = mask_a ^ mask_b;
        uint16_t mask_t1 = mask_a ^ mask_c;
        uint16_t mask_t0t1 = aux_mpc_AND2(mask_t0, mask_t1, tapes, params);

        // if (tapes->pos > 19519 && tapes->pos < 19520 + 32*4) {
        //     printf("[AUX_MAJ](%d)   mask_a = %d   mask_b = %d   mask_c = %d   mask_gamma_t0t1 = %d\n", tapes->pos, mask_a, mask_b, mask_c, mask_t0t1);
        // }

        uint16_t mask_maj = mask_t0t1 ^ mask_a;
        setMask(pmaj, 31 - i, mask_maj, state_masks);
    }
}

// void aux_FULLADDER_mpc(uint8_t a, uint8_t b, uint8_t cin, uint8_t* sum, uint8_t* cout, randomTape_t* tapes, paramset_SHA256_t* params) 
// {
//     *sum = cin ^ (a ^ b);

//     if (tapes->pos > 511 && tapes->pos < 512 + 32 * 4) {
//         printf("\n[AUX222](%d) bit_a = %d  bit_b = %d\n", tapes->pos, a, b);
//     }
    
//     // uint8_t ab = aux_mpc_AND2(a,b, tapes, params);
//     // uint8_t cin_axorb = aux_mpc_AND2(cin, a^b, tapes, params);


//     uint16_t ab = aux_mpc_AND2(a,b, tapes, params);
//     uint16_t cin_axorb = aux_mpc_AND2(cin, a^b, tapes, params);
    

//     if (tapes->pos > 511 && tapes->pos < 512 + 32 * 4) {
            
//             printf("               ab = %d   cin_axorb = %d \n", ab, cin_axorb);
//             printf("               cout = %d \n", ab ^ cin_axorb);
//     }

//     *cout = ab ^ cin_axorb;
// }

// uint32_t aux_ADD32_mpc(uint32_t a, uint32_t b, randomTape_t* tapes, paramset_SHA256_t* params)
// {
//     uint32_t res = 0;
//     uint8_t sum;
//     uint8_t cout = 0;
//     uint8_t cin;
//     uint8_t bit_a, bit_b;

//     for (int i = 0; i < 32; i++) {
//         bit_a = GETBIT(a, i);
//         bit_b = GETBIT(b, i);
//         cin = cout;

//         aux_FULLADDER_mpc(bit_a, bit_b, cin, &sum, &cout, tapes, params);
//         SETBIT(res, i, sum);
//     }
//     return res;
// }

// uint32_t aux_ADD32_mpc(uint32_t a, uint32_t b, randomTape_t* tapes, paramset_SHA256_t* params)
// {
//     if (tapes->pos > 511 && tapes->pos < 512 + 32*4) {
//         printf("[AUX](%d) mask_a = %d    mask_b = %d \n", tapes->pos, a, b);
//     }
    
//     uint8_t cin = 0;
//     uint32_t res = 0;
//     for (int i = 0; i < 32; i++) {
//         uint8_t bit_a = GETBIT(a, i);
//         uint8_t bit_b = GETBIT(b, i);

        
        

//         uint8_t sum = 0;
//         aux_FULLADDER_mpc(bit_a, bit_b, cin, &sum, &cin, tapes, params);
//         SETBIT(res, i, sum);
//     }
//     return res;
// }

static void aux_ADD32_mpc(int pa, int pb, int ps, shares_t* state_masks, randomTape_t* tapes, paramset_SHA256_t* params)
{
    uint16_t mask_cin = 0;
    for (int i = 0; i < 32; i++) {
        uint16_t mask_a = getMask(pa, 31-i, state_masks);
        uint16_t mask_b = getMask(pb, 31-i, state_masks);

        // if (tapes->pos > 511 && tapes->pos < 512 + 32*4) {
        //     printf("[AUX](%d) mask_a = %d   mask_b = %d \n", tapes->pos, mask_a, mask_b);
        // }
        

        uint16_t mask_sum = mask_cin ^ (mask_a ^ mask_b);
        setMask(ps, 31 - i, mask_sum, state_masks);

        uint16_t mask_gamma_ab = aux_mpc_AND2(mask_a, mask_b, tapes, params);
        uint16_t mask_gamma_cin_axorb = aux_mpc_AND2(mask_cin, mask_a ^ mask_b, tapes, params);

        mask_cin = mask_gamma_ab ^ mask_gamma_cin_axorb;
    }
}


// Fait comme si mask_k = 0x0000
static void aux_ADD32_K_mpc(int pa, int ps, shares_t* state_masks, randomTape_t* tapes, paramset_SHA256_t* params)
{
    uint16_t mask_cin = 0;
    for (int i = 0; i < 32; i++) {
        uint16_t mask_a = getMask(pa, 31 - i, state_masks);
        uint16_t mask_k = 0;

        // if (tapes->pos > 19135 && tapes->pos < 19136 + 32 * 4) {
        //     printf("[AUX](%d) mask_a = %d  mask_b = %d", tapes->pos, mask_a, mask_k);
        // }

        uint16_t mask_sum = mask_cin ^ (mask_a ^ mask_k);
        setMask(ps, 31 - i, mask_sum, state_masks);

        uint16_t mask_gamma_ak = aux_mpc_AND2(mask_a, mask_k, tapes, params);
        uint16_t mask_gamma_cin_axork = aux_mpc_AND2(mask_cin, mask_a ^ mask_k, tapes, params);

        // if (tapes->pos > 84479 && tapes->pos < 84480 + 32*4 ) {
        //     printf("(AUX)[%d]  mask_a = %d   mask_b = %d   mask_ab = %d   mask_cinaxorb = %d\n", tapes->pos, mask_a, mask_k, mask_gamma_ak, mask_gamma_cin_axork);
        // }

        mask_cin = mask_gamma_ak ^ mask_gamma_cin_axork;
    }
}

static void replaceMasks(int p, int pWith, shares_t* state_masks)
{
    for (int i = 0; i < 32; i++) {
        state_masks->shares[32 * p + i] = state_masks->shares[32 * pWith + i];
    }
}

// static void printMask(int p, shares_t* state_masks)
// {
//     printf("%d : ", p);
//     for (int i = 0; i < 32; i++) {
//         printf("%d ",state_masks->shares[32 * p + i]);
//     }
//     printf("\n");
// }





// Cf. picnic3-eprint.pdf Section 5.1
static void computeAuxTapeSHA256(randomTape_t* tapes, uint8_t* inputs, paramset_SHA256_t* params) {
    // Récupérer les constantes de sha256
    // uint32_t _hA[8] = { 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
	// 	0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 };

    // static const uint32_t k[64] = { 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
	// 	0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98,
	// 	0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
	// 	0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6,
	// 	0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
	// 	0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3,
	// 	0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138,
	// 	0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e,
	// 	0x92722c85, 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
	// 	0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
	// 	0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
	// 	0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814,
	// 	0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 };

    // uint8_t x[64];   // 512 bits// maj = (a & (b ^ c)) ^ (b & c);
// void aux_MAJ_mpc(uint32_t a, uint32_t b, uint32_t c, uint32_t* out, randomTape_t* tapes, paramset_SHA256_t* params)
// {
//     uint8_t t0_bit, t1_bit, a_bit, b_bit, c_bit, out_bit;
//     for (int i = 0; i < 32; i++) {
//         a_bit = GETBIT(a, i);
//         b_bit = GETBIT(b, i);
//         c_bit = GETBIT(c, i);

//         t0_bit = a_bit ^ b_bit;
//         t1_bit = a_bit ^ c_bit; 
//         out_bit = aux_mpc_AND2(t0_bit, t1_bit, tapes, params);
//         out_bit = a_bit ^ out_bit;
//         SETBIT(*out, i, out_bit);
//     }
// }
    shares_t* input_masks = allocateShares(params->inputSizeBits);
    tapesToWords(input_masks, tapes);
    shares_t* state_masks = allocateShares(params->stateSizeBits + 16);
    loadInputMasks(state_masks, input_masks);

    if (inputs != NULL) {
        // memcpy(inputs, x, params->inputSizeBits / 8);
        printf("retirer ça apres");
    }
    

    // uint32_t w[64];
	// int i;
	// for (i = 0; i < 16; i++) {
	// 	w[i] = (x[i * 4] << 24) | (x[i * 4 + 1] << 16)
	// 					| (x[i * 4 + 2] << 8) | x[i * 4 + 3];
	// }
    

    // uint32_t s0, s1, w16_s0, w7_s1;
	for (int i = 16; i < 64; i++) {
		// s0 = RIGHTROTATE(w[i - 15], 7) ^ RIGHTROTATE(w[i - 15], 18)
		// 				^ (w[i - 15] >> 3);
                        
        loadS0Masks(i, state_masks);
                        
                        
                        
        // s1 = RIGHTROTATE(w[i - 2], 17) ^ RIGHTROTATE(w[i - 2], 19)
		// 				^ (w[i - 2] >> 10);
        loadS1Masks(i, state_masks);
 
		
        
        // w[i] = w[i - 16] + s0 + w[i - 7] + s1;
        aux_ADD32_mpc(i-16, 64, 66, state_masks, tapes, params);
        aux_ADD32_mpc(i-7, 65, 67, state_masks, tapes, params);
        aux_ADD32_mpc(66, 67, i, state_masks, tapes, params);

        // w16_s0 = aux_ADD32_mpc(w[i-16], s0, tapes, params);
        // w7_s1 = aux_ADD32_mpc(w[i-7], s1, tapes, params);
        // w[i] = aux_ADD32_mpc(w16_s0, w7_s1, tapes, params);
	}


    // uint32_t a, b, c, d, e, f, g, h, temp1, temp2, maj, ch;
	// a = _hA[0];
	// b = _hA[1];
	// c = _hA[2];
	// d = _hA[3];
	// e = _hA[4];
	// f = _hA[5];
	// g = _hA[6];
	// h = _hA[7];

    // uint32_t h_s1, ch_k, chk_w; 
    for (int i = 0; i < 64; i++) {
        // temp1 = h + sig1(e) + ch(e,f,g) + k[i] + w[i]
		// s1 = RIGHTROTATE(e,6) ^ RIGHTROTATE(e, 11) ^ RIGHTROTATE(e, 25);
        loadS1Masks2(state_masks);

        aux_CH_mpc(72, 73, 74, 79, state_masks, tapes, params);

        // aux_CH_mpc(e, f, g, &ch, tapes, params);



		// temp1 = h + s1 + ch + k[i] + w[i];
        aux_ADD32_mpc(75, 65, 80, state_masks, tapes, params);
        aux_ADD32_K_mpc(79, 81, state_masks, tapes, params);  // ch_k = ch + k[i]
        aux_ADD32_mpc(81, i, 82, state_masks, tapes, params);
        aux_ADD32_mpc(80, 82, 76, state_masks, tapes, params);

        // h_s1 = aux_ADD32_mpc(h, s1, tapes, params);
        // ch_k = aux_ADD32_mpc(ch, k[i], tapes, params);
        // chk_w = aux_ADD32_mpc(ch_k, w[i], tapes, params);
        // temp1 = aux_ADD32_mpc(h_s1, chk_w, tapes, params);
        
        // temp2 = sig0(a) + maj(a,b,c)
		// s0 = RIGHTROTATE(a,2) ^ RIGHTROTATE(a, 13) ^ RIGHTROTATE(a, 22);
        loadS0Masks2(state_masks);
        
        aux_MAJ_mpc(68, 69, 70, 78, state_masks, tapes, params);

        // aux_MAJ_mpc(a, b, c, &maj ,tapes, params);

        // temp2 = s0 + maj;
        aux_ADD32_mpc(64, 78, 77, state_masks, tapes, params);

        // temp2 = aux_ADD32_mpc(s0, maj, tapes, params);

        replaceMasks(75, 74, state_masks);
        replaceMasks(74, 73, state_masks);
        replaceMasks(73, 72, state_masks);
		// h = g;
		// g = f;
		// f = e;

		// e = d + temp1;
        aux_ADD32_mpc(71, 76, 72, state_masks, tapes, params);
        // e = aux_ADD32_mpc(d, temp1, tapes, params);

        replaceMasks(71, 70, state_masks);
        replaceMasks(70, 69, state_masks);
        replaceMasks(69, 68, state_masks);
		// d = c;
		// c = b;
		// b = a;

		// a = temp1 + temp2;
        aux_ADD32_mpc(76, 77, 68, state_masks, tapes, params);
	}

    // printMask(68, state_masks);
    // printMask(69, state_masks);
    // printMask(70, state_masks);
    // printMask(71, state_masks);
    // printMask(72, state_masks);
    // printMask(73, state_masks);
    // printMask(74, state_masks);
    // printMask(75, state_masks);


    // // _hA[0] = a + _hA[0];
    aux_ADD32_K_mpc(68, 68, state_masks, tapes, params);

    // // _hA[1] = b + _hA[1];
    aux_ADD32_K_mpc(69, 69, state_masks, tapes, params);

    // // _hA[2] = c + _hA[2];
    aux_ADD32_K_mpc(70, 70, state_masks, tapes, params);

    // // _hA[3] = d + _hA[3];
    aux_ADD32_K_mpc(71, 71, state_masks, tapes, params);

    // // _hA[4] = e + _hA[4];
    aux_ADD32_K_mpc(72, 72, state_masks, tapes, params);

    // // _hA[5] = f + _hA[5];
    aux_ADD32_K_mpc(73, 73, state_masks, tapes, params);

    // // _hA[6] = g + _hA[6];
    aux_ADD32_K_mpc(74, 74, state_masks, tapes, params);

    // // _hA[7] = h + _hA[7];
    aux_ADD32_K_mpc(75, 75, state_masks, tapes, params);

    // Update la N-th (16) avec l'auxiliary information
    tapes->pos = 0;
}



static void commit(uint8_t* digest, uint8_t* seed, uint8_t* aux, uint8_t* salt, size_t t, size_t j, paramset_SHA256_t* params)
{
    /* Compute C[t][j];  as digest = H(seed||[aux]) aux is optional */
    HashInstance ctx;

    HashInit(&ctx, params, HASH_PREFIX_NONE);
    HashUpdate(&ctx, seed, params->seedSizeBytes);
    if (aux != NULL) {
        HashUpdate(&ctx, aux, params->andSizeBytes); 
    }
    HashUpdate(&ctx, salt, params->saltSizeBytes);
    HashUpdateIntLE(&ctx, t);
    HashUpdateIntLE(&ctx, j);
    HashFinal(&ctx);
    HashSqueeze(&ctx, digest, params->digestSizeBytes);
}

static void commit_h(uint8_t* digest, commitments_t* C, paramset_SHA256_t* params)
{
    HashInstance ctx;

    HashInit(&ctx, params, HASH_PREFIX_NONE);
    for (size_t i = 0; i < params->numMPCParties; i++) {
        HashUpdate(&ctx, C->hashes[i], params->digestSizeBytes);
    }
    HashFinal(&ctx);
    HashSqueeze(&ctx, digest, params->digestSizeBytes);
}

// Commit to the views for one parallel rep
static void commit_v(uint8_t* digest, uint8_t* input, msgs_t* msgs, paramset_SHA256_t* params)
{
    HashInstance ctx;

    HashInit(&ctx, params, HASH_PREFIX_NONE);
    HashUpdate(&ctx, input, 16 * sizeof(uint32_t));
    for (size_t i = 0; i < params->numMPCParties; i++) {
        size_t msgs_size = numBytes(msgs->pos);
        HashUpdate(&ctx, msgs->msgs[i], msgs_size);
    }
    HashFinal(&ctx);
    HashSqueeze(&ctx, digest, params->digestSizeBytes);
}

static void wordToMsgs(uint16_t w, msgs_t* msgs, paramset_SHA256_t* params)
{
    for (size_t i = 0; i < params->numMPCParties; i++) {
        uint8_t w_i = getBit((uint8_t*)&w, i);
        setBit(msgs->msgs[i], msgs->pos, w_i);
    }
    msgs->pos++;
}

static int contains(uint16_t* list, size_t len, size_t value)
{
    for (size_t i = 0; i < len; i++) {
        if (list[i] == value) {
            return 1;
        }
    }
    return 0;
}

static int indexOf(uint16_t* list, size_t len, size_t value)
{
    for (size_t i = 0; i < len; i++) {
        if (list[i] == value) {
            return i;
        }
    }
    assert(!"indexOf called on list where value is not found. (caller bug)");
    return -1;
}


static void getAuxBits(uint8_t* output, randomTape_t* tapes, paramset_SHA256_t* params)
{
    
    size_t last = params->numMPCParties - 1;
    size_t offset = params->inputSizeBits;
    size_t pos = 0;                               // REVOIR ÇA

    for (uint32_t j = offset; j < offset + 2 * params->andSizeBits; j++) {
        setBit(output, pos++, getBit(tapes->tape[last], j));
    }



    // for(uint32_t j = 0; j < params->numRounds; j++) {
    //     for(size_t i = 0; i < n; i++) {
    //         setBit(output, pos++, getBit(tapes->tape[last], n + n*2*j  + i));
    //     }
    // }

}



static void setAuxBits(randomTape_t* tapes, uint8_t* input, paramset_SHA256_t* params)
{
    size_t last = params->numMPCParties - 1;
    size_t offset = params->inputSizeBits;
    size_t pos = 0;                              // REVOIR ÇA

    for (uint32_t j = offset; j < offset + 2 * params->andSizeBits; j++) {
        setBit(tapes->tape[last], j, getBit(input, pos++));
    }


    // size_t last = params->numMPCParties - 1;
    // size_t pos = 0;
    // size_t n = params->stateSizeBits;

    // for(uint32_t j = 0; j < params->numRounds; j++) {
    //     for(size_t i = 0; i < n; i++) {
    //         setBit(tapes->tape[last], n + n*2*j  + i, getBit(input, pos++));
    //     }
    // }
}


// picnic3-eprint.pdf page20    
static uint8_t mpc_AND(uint8_t a, uint8_t b, uint16_t mask_a, uint16_t mask_b, uint16_t* mask_gamma, randomTape_t* tapes, msgs_t* msgs, paramset_SHA256_t* params)
{
    uint16_t output_mask = tapesToWord(tapes);
    *mask_gamma = output_mask;
    
    uint16_t and_helper = tapesToWord(tapes);   // The special mask value setup during preprocessing for each AND gate

    // [s] = z^a [lamB] XOR z^b [lamA] XOR [lamA,B] XOR [lamG]      
    uint16_t s_shares = (extend(a) & mask_b) ^ (extend(b) & mask_a) ^ and_helper ^ output_mask; 

    if (msgs->unopened >= 0) {
        uint8_t unopenedPartyBit = getBit(msgs->msgs[msgs->unopened], msgs->pos);
        setBit((uint8_t*)&s_shares, msgs->unopened, unopenedPartyBit);
    }

    // Broadcast each share of s
    wordToMsgs(s_shares, msgs, params);

    // z^g = s XOR (z^a . z^b)
    return (uint8_t)(parity16(s_shares) ^ (a & b));
}


// static void mpc_ADD32(uint32_t a, uint32_t b, uint32_t* sum, shares_t* state_masks, randomTape_t* tapes, msgs_t* msgs, paramset_SHA256_t* params)
// {
//     uint8_t cout = 0; 

//     for (int i = 0; i < 32; i++) {
//         uint8_t a_bit = GETBIT(a, i);
//         uint16_t mask_a = state_masks->shares[3*i];

//         uint8_t b_bit = GETBIT(b, i);
//         uint16_t mask_b = state_masks->shares[3*i+1];

//         uint8_t cin = cout;
//         uint16_t mask_cin = state_masks->shares[3*i+2];

//         uint8_t sum_bit = cin ^ (a_bit ^ b_bit);
//         uint16_t mask_sum = mask_cin ^ (mask_a ^ mask_b);
//         SETBIT(*sum, i, sum_bit);
//         state_masks->shares[3*i] = mask_sum; // On remplace les state masks de a par ceux de sum

//         uint16_t mask_gamma_ab; // qu'on va chercher une tape plus loin
//         uint8_t ab = mpc_AND(a, b, mask_a, mask_b, &mask_gamma_ab, tapes, msgs, params);

//         uint16_t mask_gamma_cin_axorb;
//         uint8_t cin_axorb = mpc_AND(cin, a^b, mask_cin, mask_a ^ mask_b, &mask_gamma_cin_axorb, tapes, msgs, params);

//         cout = ab ^ cin_axorb;
//         if (i < 31) {
//             // Le masque du cin suivant est celui du cout juste calculé
//             state_masks->shares[3*(i+1)+2] = mask_gamma_ab ^ mask_gamma_cin_axorb;
//         }         
//     }
// }





static void mpc_ADD32(uint32_t a, uint32_t b, uint32_t* sum, int pa, int pb, int ps, shares_t* state_masks, randomTape_t* tapes, msgs_t* msgs, paramset_SHA256_t* params)
{
    uint8_t cin = 0;
    uint16_t mask_cin = 0;


    // Indexations de masques et de GETBIT a et b inversées ATTENTION
    for (int i = 0; i < 32; i++) {
        uint8_t a_bit = GETBIT(a, i);
        uint16_t mask_a = getMask(pa, 31 - i, state_masks);

        uint8_t b_bit = GETBIT(b, i);
        uint16_t mask_b = getMask(pb, 31 - i, state_masks);

        // if (tapes->pos > 639 && tapes->pos < 640 + 32*4) {
        //     printf("[SIM](%d) MASK_A = %d   MASK_B = %d \n", tapes->pos, mask_a, mask_b);
        // }

        uint8_t sum_bit = cin ^ (a_bit ^ b_bit);
        uint16_t mask_sum = mask_cin ^ (mask_a ^ mask_b);
        SETBIT(*sum, i, sum_bit);
        setMask(ps, 31 - i, mask_sum, state_masks);

        uint16_t mask_gamma_ab;
        uint8_t ab = mpc_AND(a_bit, b_bit, mask_a, mask_b, &mask_gamma_ab, tapes, msgs, params);        

        // On doit avoir REEL(ab) = mask ^ MASQUÉ(ab), ce n'est pas le cas

        uint8_t a_xor_b = a_bit ^ b_bit;
        uint16_t mask_a_xor_b = mask_a ^ mask_b;

        uint16_t mask_gamma_cin_axorb;

        // if (tapes-> pos < 570) printf("             ab[%d] = %d   cin[%d] = %d \n", tapes->pos, ab, tapes->pos, cin);
        uint8_t cin_axorb = mpc_AND(cin, a_xor_b, mask_cin, mask_a_xor_b, &mask_gamma_cin_axorb, tapes, msgs, params);

        cin = ab ^ cin_axorb;
        mask_cin = mask_gamma_ab ^ mask_gamma_cin_axorb;

        // if (tapes->pos > 47232 && tapes->pos < 47233 + 32*4) {
        //     printf("(%d):  a_bit = %d  b_bit = %d  mask_a = %d  mask_b = %d  ab = %d  cin_axorb = %d\n", i, a_bit, b_bit, mask_a, mask_b, ab, cin_axorb);
        // }
        
    }

}


static void mpc_ADD32_K(uint32_t a, uint32_t b, uint32_t *sum, int pa, int ps, shares_t* state_masks, randomTape_t* tapes, msgs_t* msgs, paramset_SHA256_t* params)
{
    uint8_t cin = 0;
    uint16_t mask_cin = 0;

    for (int i = 0; i < 32; i++) {
        uint8_t a_bit = GETBIT(a, i);
        uint16_t mask_a = getMask(pa, 31 - i, state_masks);

        uint8_t b_bit = GETBIT(b, i);
        uint8_t mask_b = 0;

        uint8_t sum_bit = cin ^ (a_bit ^ b_bit);
        uint16_t mask_sum = mask_cin ^ (mask_a ^ mask_b);
        SETBIT(*sum, i, sum_bit);
        setMask(ps, 31 - i, mask_sum, state_masks);

        uint16_t mask_gamma_ab;
        uint8_t ab = mpc_AND(a_bit, b_bit, mask_a, mask_b, &mask_gamma_ab, tapes, msgs, params);

        uint16_t mask_gamma_cin_axorb;
        uint8_t cin_axorb = mpc_AND(cin, a_bit ^ b_bit, mask_cin, mask_a ^ mask_b, &mask_gamma_cin_axorb, tapes, msgs, params);

        // if (tapes->pos > 84479 && tapes->pos < 84480 + 32*4 ) {
        //     printf("(SIM)[%d]  MASK_A = %d   MASK_B = %d   MASK_AB = %d  MASK_CINAXORB = %d\n", tapes->pos, mask_a, mask_b, mask_gamma_ab, mask_gamma_cin_axorb);
        // }

        cin = ab ^ cin_axorb;
        mask_cin = mask_gamma_ab ^ mask_gamma_cin_axorb;
    }
}

// static void mpc_CH(uint32_t e, uint32_t f, uint32_t g, uint32_t* ch, shares_t* state_masks, randomTape_t* tapes, msgs_t* msgs, paramset_SHA256_t* params)
// {
//     for (int i = 0; i < 32; i++) {
//         uint8_t e_bit = GETBIT(e, i);
//         uint16_t mask_e = state_masks->shares[3*i]; 

//         uint8_t f_bit = GETBIT(f, i);
//         uint16_t mask_f = state_masks->shares[3*i+1];

//         uint8_t g_bit = GETBIT(g, i);
//         uint16_t mask_g = state_masks->shares[3*i+2];

//         uint8_t t0_bit = f_bit ^ g_bit;

//         uint16_t mask_gamma_et0;
//         t0_bit = mpc_AND(e_bit, t0_bit, mask_e, mask_f ^ mask_g, &mask_gamma_et0, tapes, msgs, params);

//         uint8_t ch_bit = t0_bit ^ g_bit;
//         SETBIT(*ch, i, ch_bit);
//         uint16_t mask_ch = mask_gamma_et0 ^ mask_g;
//         state_masks->shares[3*i] = mask_ch; // On remplace les state masks de e par ceux de ch
//     }
// }


// ch = [e & (f^g)] ^ g
static void mpc_CH(uint32_t e, uint32_t f, uint32_t g, uint32_t* ch, int pe, int pf, int pg, int pch, shares_t* state_masks, randomTape_t* tapes, msgs_t* msgs, paramset_SHA256_t* params)
{
    for (int i = 0; i < 32; i++) {
        uint8_t e_bit = GETBIT(e, i);
        uint16_t mask_e = getMask(pe, 31 - i, state_masks);

        uint8_t f_bit = GETBIT(f, i);
        uint16_t mask_f = getMask(pf, 31 - i, state_masks);

        uint8_t g_bit = GETBIT(g, i);
        uint16_t mask_g = getMask(pg, 31 - i, state_masks);

        uint8_t t0_bit = f_bit ^ g_bit;
        uint16_t mask_t0 = mask_f ^ mask_g;
        
        // if (tapes->pos > 20991 && tapes->pos < 20992 + 32*4) {
            // printf("[MPC_CH](%d)  ", tapes->pos);
        // }
        
        uint16_t mask_gamma_et0;
        uint8_t et0_bit = mpc_AND(e_bit, t0_bit, mask_e, mask_t0, &mask_gamma_et0, tapes, msgs, params);

        // if (tapes->pos > 20991 && tapes->pos < 20992 + 32*4) {
        //     printf("          mask_e = %d  mask_f = %d  mask_g = %d  mask_t0 = %d  mask_et0 = %d \n", mask_e, mask_f, mask_g, mask_t0, mask_gamma_et0);
        // }

        uint8_t ch_bit = et0_bit ^ g_bit;
        uint16_t mask_ch = mask_gamma_et0 ^ mask_g;

        SETBIT(*ch, i, ch_bit);
        setMask(pch, 31 - i, mask_ch, state_masks);         
    }
}

// static void mpc_MAJ(uint32_t a, uint32_t b, uint32_t c, uint32_t* maj, shares_t* state_masks, randomTape_t* tapes, msgs_t* msgs, paramset_SHA256_t* params)
// {
//     for (int i = 0; i < 32; i++) {
//         uint8_t a_bit = GETBIT(a, i);
//         uint16_t mask_a = state_masks->shares[3*i];

//         uint8_t b_bit = GETBIT(b, i);
//         uint16_t mask_b = state_masks->shares[3*i+1];

//         uint8_t c_bit = GETBIT(c, i);
//         uint16_t mask_c = state_masks->shares[3*i+2];

//         uint8_t t0_bit = a_bit ^ b_bit;
//         uint8_t t1_bit = a_bit ^ c_bit;

//         uint16_t mask_gamma_t0t1;
//         uint8_t maj_bit = mpc_AND(t0_bit, t1_bit, mask_a ^ mask_b, mask_a ^ mask_c, &mask_gamma_t0t1, tapes, msgs, params);
//         maj_bit ^= a_bit;

//         SETBIT(*maj, i, maj_bit);

//         uint16_t mask_maj = mask_a ^ mask_gamma_t0t1;
//         state_masks->shares[3*i] = mask_maj; // On remplace le state mask de a par celui de maj
//     }
// }


// maj = (a ^ b)&(a ^ c)  ^ a
static void mpc_MAJ(uint32_t a, uint32_t b, uint32_t c, uint32_t* maj, int pa, int pb, int pc, int pmaj, shares_t* state_masks, randomTape_t* tapes, msgs_t* msgs, paramset_SHA256_t* params)
{
    for (int i = 0; i < 32; i++) {
        uint8_t a_bit = GETBIT(a, i);
        uint16_t mask_a = getMask(pa, 31 - i, state_masks);

        uint8_t b_bit = GETBIT(b, i);
        uint16_t mask_b = getMask(pb, 31 - i, state_masks);

        uint8_t c_bit = GETBIT(c, i);
        uint16_t mask_c = getMask(pc, 31 - i, state_masks);

        uint8_t t0_bit = a_bit ^ b_bit;
        uint8_t t1_bit = a_bit ^ c_bit;

        uint16_t mask_gamma_t0t1;
        uint8_t maj_bit = mpc_AND(t0_bit, t1_bit, mask_a ^ mask_b, mask_a ^ mask_c, &mask_gamma_t0t1, tapes, msgs, params);
        maj_bit ^= a_bit;
        uint16_t mask_maj = mask_gamma_t0t1 ^ mask_a;

        SETBIT(*maj, i, maj_bit);
        setMask(pmaj, 31 - i, mask_maj, state_masks);

        // if (tapes->pos > 19519 && tapes->pos < 19520 + 32*4) {
        //     printf("[MPC_MAJ](%d)   mask_a = %d   mask_b = %d   mask_c = %d   mask_gamma_t0t1 = %d   maj_bit = %d\n", tapes->pos, mask_a, mask_b, mask_c, mask_gamma_t0t1, maj_bit);
        // }
    }
}

// static void loadFirst16WMasks(shares_t* mask_shares, shares_t* key_masks)
// {
//     for (int i = 0; i < 16; i++) {
//         for (int j = 0; j < 32; j++) {
//             mask_shares->shares[32*i + j] = key_masks->shares[32*i + j];
//         }
//     }
// }



// uint32_t reconstructWordMask(int p, shares_t* state_masks)
// {
//     uint32_t res;
//     uint16_t masks[32];
//     getMasks(p, masks, state_masks);
//     for (int i = 0; i < 32; i++) {
//         SETBIT(res, i, (uint8_t)parity16(masks[i]));
//     }
//     return res;
// }

uint32_t reconstructWordMask(int p, shares_t* state_masks)
{
    uint32_t mask;
    uint16_t shares[32];
    for (int i = 0; i < 32; i++) {
        shares[i] = state_masks->shares[32*p + i];
        SETBIT(mask, 31 - i, parity16(shares[i]));      // HOTFIX, bien tout mettre dans le bon sens
    }
    return mask;
}

// static void reconstructWordMask2(uint32_t* output, shares_t* shares, int p)
// {
//     for (size_t i = 0; i < 32; i++) {
//         setBitInWordArray(output, i, parity16(shares->shares[32*p + i]));
//     } 
// }

// AVEC RECONSTRUCTWORDMASK3 ON A ROTATED = S0


// static void reconstructInputShares2(uint32_t* output, shares_t* shares)
// {
//     for (size_t i = 0; i < shares->numWords; i++) {
//         setBitSO(output, i, (uint8_t)parity16(shares->shares[i]));
//     }
// }

int corr[16] = {7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8};

static void loadOutputShare(shares_t* state_masks, int p, msgs_t* msgs)
{
    for (int i = 0; i < 32; i++) {
        uint8_t share = getBit(msgs->msgs[msgs->unopened], msgs->pos + i);
        SETBIT(state_masks->shares[32*p +i], corr[msgs->unopened], share);  //changer ça
    }
    msgs->pos += 32;
}


static void broadcastOutputShares(shares_t* shares, msgs_t* msgs, paramset_SHA256_t* params)
{
    for (int p = 68; p < 76; p++) {
        for (int i = 0; i < 32; i++) {
            wordToMsgs(shares->shares[32*p + i], msgs, params);
        }
    }
}



static int simulateOnlineSHA256(uint32_t* maskedKey, randomTape_t* tapes, shares_t* input_masks, shares_t* state_masks, 
                           msgs_t* msgs, const uint32_t* publicHash, paramset_SHA256_t* params)
{

    // 16 parties
    int ret = 0;

    uint32_t _hA[8] = { 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
		0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 };

    static const uint32_t k[64] = { 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
		0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98,
		0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
		0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6,
		0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
		0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3,
		0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138,
		0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e,
		0x92722c85, 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
		0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
		0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
		0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814,
		0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 };

    char finalHash[32];


    
    // La position des tapes est déjà avancée

    // Ici, on a déjà tapesToWords dans state_masks donc les masques initiaux sont chargés, et on a encore de la tape à parcourir pour les portes AND
    // les state_masks de x sont dans w0 à w15

    /* state_masks :
            w0 à w63, s0, s1, w16_s0, w7_s1, a, b, c, d, e, f, g, h, temp1, temp2, maj, ch, h_s1, ch_k, chk_w; 
    */

    uint32_t w[64];

    int i;

    // VÉRIFIÉ
    loadInputMasks(state_masks, input_masks);
	for (i = 0; i < 16; i++) {
        w[i] = maskedKey[i];

        // if (true) {
        //     uint32_t* wmask = malloc(sizeof(uint32_t));
        //     reconstructWordMask3(wmask, state_masks, i);
        //     printf("[SIM] w[%d] = %d\n", i, *wmask ^ w[i]);
        // }
	}

    

    uint32_t s0, s1, w16_s0, w7_s1;
	for (i = 16; i < 64; i++) {
		s0 = RIGHTROTATE(w[i - 15], 7) ^ RIGHTROTATE(w[i - 15], 18)
						^ (w[i - 15] >> 3);

        loadS0Masks(i, state_masks);


		s1 = RIGHTROTATE(w[i - 2], 17) ^ RIGHTROTATE(w[i - 2], 19)
						^ (w[i - 2] >> 10);

        loadS1Masks(i, state_masks);


		// w[i] = w[i - 16] + s0 + w[i - 7] + s1;
        mpc_ADD32(w[i-16], s0, &w16_s0, i - 16, 64, 66, state_masks, tapes, msgs, params);
        
        mpc_ADD32(w[i-7], s1, &w7_s1, i-7, 65, 67, state_masks, tapes, msgs, params);
        
        mpc_ADD32(w16_s0, w7_s1, &w[i], 66, 67, i, state_masks, tapes, msgs, params);
	}


    uint32_t a, b, c, d, e, f, g, h, temp1, temp2, maj, ch;               
	a = _hA[0];
	b = _hA[1];
	c = _hA[2];
	d = _hA[3];
	e = _hA[4];
	f = _hA[5];
	g = _hA[6];
	h = _hA[7];
    maj = 0;
    ch = 0;

    uint32_t h_s1, ch_k, chk_w;
    for (i = 0; i < 64; i++) {
        // temp1 = h + sig1(e) + ch(e,f,g) + k[i] + w[i]
        s1 = RIGHTROTATE(e,6) ^ RIGHTROTATE(e, 11) ^ RIGHTROTATE(e, 25);  
        loadS1Masks2(state_masks);
       
        mpc_CH(e, f, g, &ch, 72, 73, 74, 79, state_masks, tapes, msgs, params);


        // temp1 = h + s1 + ch + k[i] + w[i];
        mpc_ADD32(h, s1, &h_s1, 75, 65, 80, state_masks, tapes, msgs, params);

        mpc_ADD32_K(ch, k[i], &ch_k, 79, 81, state_masks, tapes, msgs, params); 

        mpc_ADD32(ch_k, w[i], &chk_w, 81, i, 82, state_masks, tapes, msgs, params);

        mpc_ADD32(h_s1, chk_w, &temp1, 80, 82, 76, state_masks, tapes, msgs, params);


        // temp2 = sig0(a) + maj(a,b,c)
		s0 = RIGHTROTATE(a,2) ^ RIGHTROTATE(a, 13) ^ RIGHTROTATE(a, 22);
        loadS0Masks2(state_masks);

        mpc_MAJ(a, b, c, &maj, 68, 69, 70, 78, state_masks, tapes, msgs, params);

        mpc_ADD32(s0, maj, &temp2, 64, 78, 77, state_masks, tapes, msgs, params);


        h = g;
        replaceMasks(75, 74, state_masks);

		g = f;
        replaceMasks(74, 73, state_masks);

		f = e;
        replaceMasks(73, 72, state_masks);


        // e = d + temp1
        mpc_ADD32(d, temp1, &e, 71, 76, 72, state_masks, tapes, msgs, params);


		d = c;
        replaceMasks(71, 70, state_masks);

		c = b;
        replaceMasks(70, 69, state_masks);

		b = a;
        replaceMasks(69, 68, state_masks);


        // a = temp1 + temp2
        mpc_ADD32(temp1, temp2, &a, 76, 77, 68, state_masks, tapes, msgs, params);
    }

    mpc_ADD32_K(a, _hA[0], &a, 68, 68, state_masks, tapes, msgs, params);
    mpc_ADD32_K(b, _hA[1], &b, 69, 69, state_masks, tapes, msgs, params);
    mpc_ADD32_K(c, _hA[2], &c, 70, 70, state_masks, tapes, msgs, params);
    mpc_ADD32_K(d, _hA[3], &d, 71, 71, state_masks, tapes, msgs, params);
    mpc_ADD32_K(e, _hA[4], &e, 72, 72, state_masks, tapes, msgs, params);
    mpc_ADD32_K(f, _hA[5], &f, 73, 73, state_masks, tapes, msgs, params);
    mpc_ADD32_K(g, _hA[6], &g, 74, 74, state_masks, tapes, msgs, params);
    mpc_ADD32_K(h, _hA[7], &h, 75, 75, state_masks, tapes, msgs, params);


    if (msgs->unopened >= 0) {
        printf("DEBUT LOADOUTPUTSHARES\n");
        loadOutputShare(state_masks, 68, msgs);
        loadOutputShare(state_masks, 69, msgs);
        loadOutputShare(state_masks, 70, msgs);
        loadOutputShare(state_masks, 71, msgs);
        loadOutputShare(state_masks, 72, msgs);
        loadOutputShare(state_masks, 73, msgs);
        loadOutputShare(state_masks, 74, msgs);
        loadOutputShare(state_masks, 75, msgs);
        printf("FIN LOADOUTPUTSHARES \n");
    }
    
    broadcastOutputShares(state_masks, msgs, params);

    /* Démasquage */
    uint32_t* amask = malloc(sizeof(uint32_t));
    uint32_t* bmask = malloc(sizeof(uint32_t));
    uint32_t* cmask = malloc(sizeof(uint32_t));
    uint32_t* dmask = malloc(sizeof(uint32_t));
    uint32_t* emask = malloc(sizeof(uint32_t));
    uint32_t* fmask = malloc(sizeof(uint32_t));
    uint32_t* gmask = malloc(sizeof(uint32_t));
    uint32_t* hmask = malloc(sizeof(uint32_t));

    reconstructWordMask3(amask, state_masks, 68);
    reconstructWordMask3(bmask, state_masks, 69);
    reconstructWordMask3(cmask, state_masks, 70);
    reconstructWordMask3(dmask, state_masks, 71);
    reconstructWordMask3(emask, state_masks, 72);
    reconstructWordMask3(fmask, state_masks, 73);
    reconstructWordMask3(gmask, state_masks, 74);
    reconstructWordMask3(hmask, state_masks, 75);

    printf("amask = %d  bmask = %d  cmask = %d  dmask = %d  emask = %d  fmask = %d  gmask = %d  hmask = %d\n", *amask, *bmask, *cmask, *dmask, *emask, *fmask, *gmask, *hmask);

    // printf("[SIM] a = %d   b = %d   c = %d   d = %d   e = %d   f = %d   g = %d   h = %d\n", *amask ^ a, *bmask ^ b, *cmask ^ c, *dmask ^ d, *emask ^ e, *fmask ^ f, *gmask ^ g, *hmask ^ h);
    

    // Ouput de 256 bits : out_h0 | out_h1 | out_h2 | .. | out_h7
    uint32_t out_hA[8];
    out_hA[0] = *amask ^ a;
    out_hA[1] = *bmask ^ b;
    out_hA[2] = *cmask ^ c;
    out_hA[3] = *dmask ^ d;
    out_hA[4] = *emask ^ e;
    out_hA[5] = *fmask ^ f;
    out_hA[6] = *gmask ^ g;
    out_hA[7] = *hmask ^ h;


    for (i = 0; i < 8; i++) {
		finalHash[i * 4] = (out_hA[i] >> 24);
		finalHash[i * 4 + 1] = (out_hA[i] >> 16);
		finalHash[i * 4 + 2] = (out_hA[i] >> 8);
		finalHash[i * 4 + 3] = out_hA[i];
	}

    printHex("Hash calculé", (uint8_t*)finalHash, 32);
    printf("\n\n\n");

    if (memcmp(finalHash, publicHash, params->stateSizeBytes) != 0) {
        ret = -1;
    }

    return ret;
}


static size_t bitsToChunks(size_t chunkLenBits, const uint8_t* input, size_t inputLen, uint16_t* chunks)
{
    if (chunkLenBits > inputLen * 8) {
        assert(!"Invalid input to bitsToChunks: not enough input");
        return 0;
    }
    size_t chunkCount = ((inputLen * 8) / chunkLenBits);

    for (size_t i = 0; i < chunkCount; i++) {
        chunks[i] = 0;
        for (size_t j = 0; j < chunkLenBits; j++) {
            chunks[i] += getBit(input, i * chunkLenBits + j) << j;
            assert(chunks[i] < (1 << chunkLenBits));
        }
        chunks[i] = fromLittleEndian(chunks[i]);
    }

    return chunkCount;
}

static size_t appendUnique(uint16_t* list, uint16_t value, size_t position)
{
    if (position == 0) {
        list[position] = value;
        return position + 1;
    }

    for (size_t i = 0; i < position; i++) {
        if (list[i] == value) {
            return position;
        }
    }
    list[position] = value;
    return position + 1;
}


static void expandChallengeHash(uint8_t* challengeHash, uint16_t* challengeC, uint16_t* challengeP, paramset_SHA256_t* params)
{
    HashInstance ctx;
    // Populate C
    uint32_t bitsPerChunkC = ceil_log2(params->numMPCRounds);
    uint32_t bitsPerChunkP = ceil_log2(params->numMPCParties);
    uint16_t* chunks = calloc(params->digestSizeBytes * 8 / MIN(bitsPerChunkC, bitsPerChunkP), sizeof(uint16_t));
    uint8_t h[MAX_DIGEST_SIZE];

    memcpy(h, challengeHash, params->digestSizeBytes);

    size_t countC = 0;
    while (countC < params->numOpenedRounds) {
        size_t numChunks = bitsToChunks(bitsPerChunkC, h, params->digestSizeBytes, chunks);
        for (size_t i = 0; i < numChunks; i++) {
            if (chunks[i] < params->numMPCRounds) {
                countC = appendUnique(challengeC, chunks[i], countC);
            }
            if (countC == params->numOpenedRounds) {
                break;
            }
        }

        HashInit(&ctx, params, HASH_PREFIX_1);
        HashUpdate(&ctx, h, params->digestSizeBytes);
        HashFinal(&ctx);
        HashSqueeze(&ctx, h, params->digestSizeBytes);
    }

    // Note that we always compute h = H(h) after setting C
    size_t countP = 0;

    while (countP < params->numOpenedRounds) {
        size_t numChunks = bitsToChunks(bitsPerChunkP, h, params->digestSizeBytes, chunks);
        for (size_t i = 0; i < numChunks; i++) {
            if (chunks[i] < params->numMPCParties) {
                challengeP[countP] = chunks[i];
                countP++;
            }
            if (countP == params->numOpenedRounds) {
                break;
            }
        }

        HashInit(&ctx, params, HASH_PREFIX_1);
        HashUpdate(&ctx, h, params->digestSizeBytes);
        HashFinal(&ctx);
        HashSqueeze(&ctx, h, params->digestSizeBytes);
    }

#if 0   // Print challenge when debugging
    printHex("challengeHash", challengeHash, params->digestSizeBytes);
#endif

    free(chunks);
}

static void HCP(uint8_t* challengeHash, uint16_t* challengeC, uint16_t* challengeP, commitments_t* Ch,
                uint8_t* hCv, uint8_t* salt, const uint32_t* publicHash, paramset_SHA256_t* params)
{
    HashInstance ctx;

    assert(params->numOpenedRounds < params->numMPCRounds);


    HashInit(&ctx, params, HASH_PREFIX_NONE);
    for (size_t t = 0; t < params->numMPCRounds; t++) {
        HashUpdate(&ctx, Ch->hashes[t], params->digestSizeBytes);
    }

    HashUpdate(&ctx, hCv, params->digestSizeBytes);
    HashUpdate(&ctx, salt, params->saltSizeBytes);
    HashUpdate(&ctx, (uint8_t*)publicHash, params->stateSizeBytes);
    HashFinal(&ctx);
    HashSqueeze(&ctx, challengeHash, params->digestSizeBytes);

    if((challengeC != NULL) && (challengeP != NULL)) {
        expandChallengeHash(challengeHash, challengeC, challengeP, params);
    }
}

// static void reconstructShares(uint32_t* output, shares_t* shares)
// {
//     for (size_t i = 0; i < shares->numWords; i++) {
//         setBitInWordArray(output, i, parity16(shares->shares[i]));
//     }
// }


static uint16_t* getMissingLeavesList(uint16_t* challengeC, paramset_SHA256_t* params)
{
    size_t missingLeavesSize = params->numMPCRounds - params->numOpenedRounds;
    uint16_t* missingLeaves = calloc(missingLeavesSize, sizeof(uint16_t));
    size_t pos = 0;

    for (size_t i = 0; i < params->numMPCRounds; i++) {
        if (!contains(challengeC, params->numOpenedRounds, i)) {
            missingLeaves[pos] = i;
            pos++;
        }
    }

    return missingLeaves;
}

void printInput(uint32_t* inputs) {
    for (int u = 0; u < 16; u++) {
        printf("%d  -  ", inputs[u]);
    }
}

void printInput2(uint8_t* inputs) {
    for (int u = 0; u < 32; u++) {
        printf("%d ", inputs[u]);
    }
}


int verify_picnic3(signature2_t* sig, const uint32_t* publicHash, paramset_SHA256_t* params)
{

    commitments_t* C = allocateCommitments(params, 0);
    commitments_t Ch = { 0 };
    commitments_t Cv = { 0 };
    msgs_t* msgs = allocateMsgs(params);
    tree_t* treeCv = createTree(params->numMPCRounds, params->digestSizeBytes);
    uint8_t challengeHash[MAX_DIGEST_SIZE];
    tree_t** seeds = calloc(params->numMPCRounds, sizeof(tree_t*));
    randomTape_t* tapes = malloc(params->numMPCRounds * sizeof(randomTape_t));
    tree_t* iSeedsTree = createTree(params->numMPCRounds, params->seedSizeBytes);


    //  [  2  ]
    int ret = reconstructSeeds(iSeedsTree, sig->challengeC, params->numOpenedRounds, sig->iSeedInfo, sig->iSeedInfoLen, sig->salt, 0, params);
    if (ret != 0) {
        ret = -1;
        goto Exit;
    }

    // [  3  ]
    /* Populate seeds with values from the signature */
    for (size_t t = 0; t < params->numMPCRounds; t++) {
        if (!contains(sig->challengeC, params->numOpenedRounds, t)) {
            /* Expand iSeed[t] to seeds for each parties, using a seed tree */
            seeds[t] = generateSeeds(params->numMPCParties, getLeaf(iSeedsTree, t), sig->salt, t, params);
        }
        else {
            /* We don't have the initial seed for the round, but instead a seed
             * for each unopened party */
            seeds[t] = createTree(params->numMPCParties, params->seedSizeBytes);
            size_t P_index = indexOf(sig->challengeC, params->numOpenedRounds, t);
            uint16_t hideList[1];
            hideList[0] = sig->challengeP[P_index];
            ret = reconstructSeeds(seeds[t], hideList, 1,
                                   sig->proofs[t].seedInfo, sig->proofs[t].seedInfoLen,
                                   sig->salt, t, params);
            if (ret != 0) {
                ret = -1;
                goto Exit;
            }
        }
    }

    /* Commit */
    size_t last = params->numMPCParties - 1;
    uint8_t auxBits[MAX_AUX_BYTES] = {0,};
    for (size_t t = 0; t < params->numMPCRounds; t++) {
        /* Compute random tapes for all parties.  One party for each repitition
         * challengeC will have a bogus seed; but we won't use that party's
         * random tape. */

        createRandomTapes(&tapes[t], getLeaves(seeds[t]), sig->salt, t, params);

        if (!contains(sig->challengeC, params->numOpenedRounds, t)) {
            /* We're given iSeed, have expanded the seeds, compute aux from scratch so we can comnpte Com[t] */
            computeAuxTapeSHA256(&tapes[t], NULL, params);
            for (size_t j = 0; j < last; j++) {
                commit(C[t].hashes[j], getLeaf(seeds[t], j), NULL, sig->salt, t, j, params);
            }
            getAuxBits(auxBits, &tapes[t], params);                    //modifier (LowMC)
            commit(C[t].hashes[last], getLeaf(seeds[t], last), auxBits, sig->salt, t, last, params);
        }
        else {
            /* We're given all seeds and aux bits, execpt for the unopened 
             * party, we get their commitment */
            size_t unopened = sig->challengeP[indexOf(sig->challengeC, params->numOpenedRounds, t)];
            for (size_t j = 0; j < last; j++) {
                if (j != unopened) {
                    commit(C[t].hashes[j], getLeaf(seeds[t], j), NULL, sig->salt, t, j, params);
                }
            }
            if (last != unopened) {
                commit(C[t].hashes[last], getLeaf(seeds[t], last), sig->proofs[t].aux, sig->salt, t, last, params);
            }

            memcpy(C[t].hashes[unopened], sig->proofs[t].C, params->digestSizeBytes);
        }

       

    }

    /* Commit to the commitments */
    allocateCommitments2(&Ch, params, params->numMPCRounds);
    for (size_t t = 0; t < params->numMPCRounds; t++) {
        commit_h(Ch.hashes[t], &C[t], params);
    }

    

    /* Commit to the views */
    allocateCommitments2(&Cv, params, params->numMPCRounds);
    shares_t* state_masks = allocateShares(params->stateSizeBits + 16);
    shares_t* input_masks = allocateShares(params->inputSizeBits);
    for (size_t t = 0; t < params->numMPCRounds; t++) {
        

        if (contains(sig->challengeC, params->numOpenedRounds, t)) {
            /* 2. When t is in C, we have everything we need to re-compute the view, as an honest signer would.
             * We simulate the MPC with one fewer party; the unopned party's values are all set to zero. */
            size_t unopened = sig->challengeP[indexOf(sig->challengeC, params->numOpenedRounds, t)];
            size_t tapeLengthBytes = getTapeSizeBytes(params);

            if(unopened != last) {  // sig->proofs[t].aux is only set when P_t != N
                setAuxBits(&tapes[t], sig->proofs[t].aux, params);
            }


            memset(tapes[t].tape[unopened], 0, tapeLengthBytes);

            memcpy(msgs[t].msgs[unopened], sig->proofs[t].msgs, params->andSizeBytes);
            msgs[t].unopened = unopened;

            printf("UNOPENED: %ld\n", unopened);

            tapesToWords(input_masks, &tapes[t]);

            int rv = simulateOnlineSHA256((uint32_t*)sig->proofs[t].input, &tapes[t], input_masks, state_masks, &msgs[t], publicHash, params);
            if (rv != 0) {
                freeShares(input_masks);
                ret = -1;
                goto Exit;
            }
            commit_v(Cv.hashes[t], sig->proofs[t].input, &msgs[t], params);
        }
        else {
            Cv.hashes[t] = NULL;
        }
    }
    freeShares(state_masks);

    size_t missingLeavesSize = params->numMPCRounds - params->numOpenedRounds;
    uint16_t* missingLeaves = getMissingLeavesList(sig->challengeC, params);
    ret = addMerkleNodes(treeCv, missingLeaves, missingLeavesSize, sig->cvInfo, sig->cvInfoLen);
    free(missingLeaves);
    if (ret != 0) {
        ret = -1;
        goto Exit;
    }

    ret = verifyMerkleTree(treeCv, Cv.hashes, sig->salt, params);
    if (ret != 0) {
        ret = -1;
        goto Exit;
    }

    /* Compute the challenge hash */
    HCP(challengeHash, NULL, NULL, &Ch, treeCv->nodes[0], sig->salt, publicHash, params);

    /* Compare to challenge from signature */
    if ( memcmp(sig->challengeHash, challengeHash, params->digestSizeBytes) != 0) {
        ret = -1;
        goto Exit;
    }

    ret = EXIT_SUCCESS;

Exit:

    freeCommitments(C);
    freeCommitments2(&Cv);
    freeCommitments2(&Ch);
    freeMsgs(msgs);
    freeTree(treeCv);
    freeTree(iSeedsTree);
    for (size_t t = 0; t < params->numMPCRounds; t++) {
        freeRandomTape(&tapes[t]);
        freeTree(seeds[t]);
    }
    free(seeds);
    free(tapes);

    return ret;
}

static void computeSaltAndRootSeed(uint8_t* saltAndRoot, size_t saltAndRootLength, uint32_t* witness, uint32_t* publicHash, paramset_SHA256_t* params)
{
    HashInstance ctx;
    
    HashInit(&ctx, params, HASH_PREFIX_NONE);
    HashUpdate(&ctx, (uint8_t*)witness, params->inputSizeBits / 8);
    HashUpdate(&ctx, (uint8_t*)publicHash, 32);
    HashUpdateIntLE(&ctx, params->stateSizeBits);   // ?
    HashFinal(&ctx);
    HashSqueeze(&ctx, saltAndRoot, saltAndRootLength);
}

// static void printMaskedKey(uint32_t* maskedKey) {
//     for (int i = 0; i < 16; i++) {
//         printf("%d", maskedKey[i]);
//         fflush(stdout);
//     }
// }


static void reconstructInputMasks(uint32_t* out, shares_t* input_masks)
{
    for (size_t i = 0; i < 16; i++) {
        reconstructWordMask3(&out[i], input_masks, i);
    }
}

// PARTIE INTERESSANTE 19/05
// spec-v3.0.pdf Section 7.1
int sign_picnic3(uint32_t* witness, uint32_t* publicHash, signature2_t* sig, paramset_SHA256_t* params)
{
    int ret = 0;
    // [  1  ]
    tree_t* treeCv = NULL;
    commitments_t Ch = {0};
    commitments_t Cv = {0};
    uint8_t* saltAndRoot = malloc(params->saltSizeBytes + params->seedSizeBytes);

    // [  2  ]
    computeSaltAndRootSeed(saltAndRoot, params->saltSizeBytes + params->seedSizeBytes, witness, publicHash, params);
    memcpy(sig->salt, saltAndRoot, params->saltSizeBytes);

    // [  3  ]
    tree_t* iSeedsTree = generateSeeds(params->numMPCRounds, saltAndRoot + params->saltSizeBytes, sig->salt, 0, params);
    uint8_t** iSeeds = getLeaves(iSeedsTree);  
    free(saltAndRoot);   

    
    // [  1  ]
    randomTape_t* tapes = malloc(params->numMPCRounds * sizeof(randomTape_t));  // 1 `tapes` par exécution
    

    // [  3  ]
    tree_t** seeds = malloc(params->numMPCRounds * sizeof(tree_t*));

    // [  4  ]
    for (size_t t = 0; t < params->numMPCRounds; t++) {
        // [  4.a  ]
        seeds[t] = generateSeeds(params->numMPCParties, iSeeds[t], sig->salt, t, params);   

        // [  4.b  ]
        createRandomTapes(&tapes[t], getLeaves(seeds[t]), sig->salt, t, params);  
    }


    /* Preprocessing; compute aux tape for the N-th player, for each parallel rep */
    // inputs_t inputs = allocateInputs(params);   !!!
    uint8_t auxBits[MAX_AUX_BYTES] = {0,};

    // [  4.c  ]
    for (size_t t = 0; t < params->numMPCRounds; t++) {
        // computeAuxTapeSHA256(&tapes[t], inputs[t], params);
        computeAuxTapeSHA256(&tapes[t], NULL, params);
    }

    /* Commit to seeds and aux bits */ 
    // [  4.d  ]
    commitments_t* C = allocateCommitments(params, 0);
    for (size_t t = 0; t < params->numMPCRounds; t++) {
        for (size_t j = 0; j < params->numMPCParties - 1; j++) {
            commit(C[t].hashes[j], getLeaf(seeds[t], j), NULL, sig->salt, t, j, params);
        }
        size_t last = params->numMPCParties - 1;

        getAuxBits(auxBits, &tapes[t], params);
        commit(C[t].hashes[last], getLeaf(seeds[t], last), auxBits, sig->salt, t, last, params);
    }

    /* Simulate the online phase of the MPC */
    msgs_t* msgs = allocateMsgs(params);
    shares_t* state_masks = allocateShares(params->stateSizeBits + 16);
    shares_t* input_masks = allocateShares(params->inputSizeBits);
    inputs_t inputs = allocateInputs2(params);
    for (size_t t = 0; t < params->numMPCRounds; t++) {

        uint32_t* maskedKey = malloc (16 * sizeof(uint32_t));
        uint32_t* inputMask = malloc (16 * sizeof(uint32_t));
        // uint32_t* maskedKey = malloc (params->inputSizeBits); 


        // TRICHE
        witness[0] = 1633837924;
        witness[1] = 1701209960;
        witness[2] = 2147483648;
        witness[3] = 0;
        witness[4] = 0;
        witness[5] = 0;
        witness[6] = 0;
        witness[7] = 0;
        witness[8] = 0;
        witness[9] = 0;
        witness[10] = 0;
        witness[11] = 0;
        witness[12] = 0;
        witness[13] = 0;
        witness[14] = 0;
        witness[15] = 64;

        // [  4.e  ]
        tapesToWords(input_masks, &tapes[t]);
        reconstructInputMasks(inputMask, input_masks);

        for (int u = 0; u < 16; u++) {
            maskedKey[u] = inputMask[u] ^ witness[u];
        }

        memcpy(inputs[t], maskedKey, 16*sizeof(uint32_t));

        // printf("[SIGN](%ld) InputMasks: ", t);
        // printInputMasks(input_masks);
        // printf("\n");

        // [  4.f  ]
        int rv = simulateOnlineSHA256(maskedKey, &tapes[t], input_masks, state_masks, &msgs[t], publicHash, params);
        if (rv != 0) {
            freeShares(state_masks);
            ret = -1;
            goto Exit;
        }
    }
    // freeShares(input_masks)
    freeShares(state_masks);


    /* Commit to the commitments and views */
    // [  4.g  & 4.h  ]
    allocateCommitments2(&Ch, params, params->numMPCRounds);
    allocateCommitments2(&Cv, params, params->numMPCRounds);
    for (size_t t = 0; t < params->numMPCRounds; t++) {
        commit_h(Ch.hashes[t], &C[t], params);
    
        commit_v(Cv.hashes[t], inputs[t], &msgs[t], params);
    }

    /* Create a Merkle tree with Cv as the leaves */
    // [  5  ]
    treeCv = createTree(params->numMPCRounds, params->digestSizeBytes);
    buildMerkleTree(treeCv, Cv.hashes, sig->salt, params);

    /* Compute the challenge; two lists of integers */
    // [  6  ]
    uint16_t* challengeC = sig->challengeC;
    uint16_t* challengeP = sig->challengeP;
    HCP(sig->challengeHash, challengeC, challengeP, &Ch, treeCv->nodes[0], sig->salt, publicHash, params);

    /* Send information required for checking commitments with Merkle tree.
     * The commitments the verifier will be missing are those not in challengeC. */
    // [  7  ]
    size_t missingLeavesSize = params->numMPCRounds - params->numOpenedRounds;
    uint16_t* missingLeaves = getMissingLeavesList(challengeC, params);
    size_t cvInfoLen = 0;
    uint8_t* cvInfo = openMerkleTree(treeCv, missingLeaves, missingLeavesSize, &cvInfoLen);
    sig->cvInfo = cvInfo;
    sig->cvInfoLen = cvInfoLen;
    free(missingLeaves);

    /* Reveal iSeeds for unopned rounds, those in {0..T-1} \ ChallengeC. */
    // [  8  ]
    sig->iSeedInfo = malloc(params->numMPCRounds * params->seedSizeBytes);
    sig->iSeedInfoLen = revealSeeds(iSeedsTree, challengeC, params->numOpenedRounds,
                                    sig->iSeedInfo, params->numMPCRounds * params->seedSizeBytes, params);
    sig->iSeedInfo = realloc(sig->iSeedInfo, sig->iSeedInfoLen);

    /* Assemble the proof */
    // [  9 & 10  ]
    proof2_t* proofs = sig->proofs;
    for (size_t t = 0; t < params->numMPCRounds; t++) {
        if (contains(challengeC, params->numOpenedRounds, t)) {
            allocateProof2(&proofs[t], params);
            size_t P_index = indexOf(challengeC, params->numOpenedRounds, t);

            uint16_t hideList[1];
            hideList[0] = challengeP[P_index];
            proofs[t].seedInfo = malloc(params->numMPCParties * params->seedSizeBytes);
            proofs[t].seedInfoLen = revealSeeds(seeds[t], hideList, 1, proofs[t].seedInfo, params->numMPCParties * params->seedSizeBytes, params);
            proofs[t].seedInfo = realloc(proofs[t].seedInfo, proofs[t].seedInfoLen);

            size_t last = params->numMPCParties - 1;
            if (challengeP[P_index] != last) {
                getAuxBits(proofs[t].aux, &tapes[t], params);
            }

            memcpy(proofs[t].input, inputs[t], 16 * sizeof(uint32_t));
            
            // printf("\nMsgs(%ld)[%d]: ", t, challengeP[P_index]);
            // printMsgs(msgs[t].msgs[challengeP[P_index]]);
            // printf("\n");


            memcpy(proofs[t].msgs, msgs[t].msgs[challengeP[P_index]], params->andSizeBytes);
            memcpy(proofs[t].C, C[t].hashes[challengeP[P_index]], params->digestSizeBytes);
        }
    }

    sig->proofs = proofs;

Exit: 

    for (size_t t = 0; t < params->numMPCRounds; t++) {
        freeRandomTape(&tapes[t]);
        freeTree(seeds[t]);
    }
    free(tapes);
    free(seeds);
    freeTree(iSeedsTree);
    freeTree(treeCv);

    freeCommitments(C);
    freeCommitments2(&Ch);
    freeCommitments2(&Cv);
    freeInputs(inputs);
    freeMsgs(msgs);

    return ret;


}

int deserializeSignature2(signature2_t* sig, const uint8_t* sigBytes, size_t sigBytesLen, paramset_SHA256_t* params)
{
    /* Read the challenge and salt */
    size_t bytesRequired = params->digestSizeBytes + params->saltSizeBytes;

    if (sigBytesLen < bytesRequired) {
        return EXIT_FAILURE;
    }


    memcpy(sig->challengeHash, sigBytes, params->digestSizeBytes);
    sigBytes += params->digestSizeBytes;
    memcpy(sig->salt, sigBytes, params->saltSizeBytes);
    sigBytes += params->saltSizeBytes;

    expandChallengeHash(sig->challengeHash, sig->challengeC, sig->challengeP, params);

    /* Add size of iSeeds tree data */
    sig->iSeedInfoLen = revealSeedsSize(params->numMPCRounds, sig->challengeC, params->numOpenedRounds, params);
    bytesRequired += sig->iSeedInfoLen;

    /* Add the size of the Cv Merkle tree data */
    size_t missingLeavesSize = params->numMPCRounds - params->numOpenedRounds;
    uint16_t* missingLeaves = getMissingLeavesList(sig->challengeC, params);
    sig->cvInfoLen = openMerkleTreeSize(params->numMPCRounds, missingLeaves, missingLeavesSize, params);
    bytesRequired += sig->cvInfoLen;
    free(missingLeaves);

    /* Compute the number of bytes required for the proofs */
    uint16_t hideList[1] = { 0 };
    size_t seedInfoLen = revealSeedsSize(params->numMPCParties, hideList, 1, params);
    for (size_t t = 0; t < params->numMPCRounds; t++) {
        if (contains(sig->challengeC, params->numOpenedRounds, t)) {
            size_t P_t = sig->challengeP[indexOf(sig->challengeC, params->numOpenedRounds, t)];
            if (P_t != (params->numMPCParties - 1)) {
                bytesRequired += params->andSizeBytes;
            }
            bytesRequired += seedInfoLen;
            bytesRequired += params->stateSizeBytes;
            bytesRequired += params->andSizeBytes;
            bytesRequired += params->digestSizeBytes;
        }
    }

    /* Fail if the signature does not have the exact number of bytes we expect */
    if (sigBytesLen != bytesRequired) {
        return EXIT_FAILURE;
    }

    sig->iSeedInfo = malloc(sig->iSeedInfoLen);
    memcpy(sig->iSeedInfo, sigBytes, sig->iSeedInfoLen);
    sigBytes += sig->iSeedInfoLen;

    sig->cvInfo = malloc(sig->cvInfoLen);
    memcpy(sig->cvInfo, sigBytes, sig->cvInfoLen);
    sigBytes += sig->cvInfoLen;

    /* Read the proofs */
    for (size_t t = 0; t < params->numMPCRounds; t++) {
        if (contains(sig->challengeC, params->numOpenedRounds, t)) {
            allocateProof2(&sig->proofs[t], params);
            sig->proofs[t].seedInfoLen = seedInfoLen;
            sig->proofs[t].seedInfo = malloc(sig->proofs[t].seedInfoLen);
            memcpy(sig->proofs[t].seedInfo, sigBytes, sig->proofs[t].seedInfoLen);
            sigBytes += sig->proofs[t].seedInfoLen;

            size_t P_t = sig->challengeP[indexOf(sig->challengeC, params->numOpenedRounds, t)];
            if (P_t != (params->numMPCParties - 1) ) {
                memcpy(sig->proofs[t].aux, sigBytes, params->andSizeBytes);
                sigBytes += params->andSizeBytes;
                if (!arePaddingBitsZero(sig->proofs[t].aux, 3 /* * params->numRounds * params->numSboxes */ )) {
                    return -1;
                }
            }

            memcpy(sig->proofs[t].input, sigBytes, params->stateSizeBytes);
            sigBytes += params->stateSizeBytes;

            size_t msgsByteLength = params->andSizeBytes;
            memcpy(sig->proofs[t].msgs, sigBytes, msgsByteLength);
            sigBytes += msgsByteLength;
            size_t msgsBitLength =  3;// * params->numRounds * params->numSboxes;
            if (!arePaddingBitsZero(sig->proofs[t].msgs, msgsBitLength)) {
                return -1;
            }

            memcpy(sig->proofs[t].C, sigBytes, params->digestSizeBytes);
            sigBytes += params->digestSizeBytes;
        }
    }

    return EXIT_SUCCESS;
}

int serializeSignature2(const signature2_t* sig, uint8_t* sigBytes, size_t sigBytesLen, paramset_SHA256_t* params)
{
    uint8_t* sigBytesBase = sigBytes;

    /* Compute the number of bytes required for the signature */
    size_t bytesRequired = params->digestSizeBytes + params->saltSizeBytes;     /* challenge and salt */

    bytesRequired += sig->iSeedInfoLen;     /* Encode only iSeedInfo, the length will be recomputed by deserialize */
    bytesRequired += sig->cvInfoLen;

    for (size_t t = 0; t < params->numMPCRounds; t++) {   /* proofs */
        if (contains(sig->challengeC, params->numOpenedRounds, t)) {
            size_t P_t = sig->challengeP[indexOf(sig->challengeC, params->numOpenedRounds, t)];
            bytesRequired += sig->proofs[t].seedInfoLen;
            if (P_t != (params->numMPCParties - 1)) {
                bytesRequired += params->andSizeBytes;
            }
            bytesRequired += params->stateSizeBytes;
            bytesRequired += params->andSizeBytes;
            bytesRequired += params->digestSizeBytes;
        }
    }

    if (sigBytesLen < bytesRequired) {
        return -1;
    }

    memcpy(sigBytes, sig->challengeHash, params->digestSizeBytes);
    sigBytes += params->digestSizeBytes;

    memcpy(sigBytes, sig->salt, params->saltSizeBytes);
    sigBytes += params->saltSizeBytes;

    memcpy(sigBytes, sig->iSeedInfo, sig->iSeedInfoLen);
    sigBytes += sig->iSeedInfoLen;
    memcpy(sigBytes, sig->cvInfo, sig->cvInfoLen);
    sigBytes += sig->cvInfoLen;

    /* Write the proofs */
    for (size_t t = 0; t < params->numMPCRounds; t++) {
        if (contains(sig->challengeC, params->numOpenedRounds, t)) {
            memcpy(sigBytes, sig->proofs[t].seedInfo,  sig->proofs[t].seedInfoLen);
            sigBytes += sig->proofs[t].seedInfoLen;

            size_t P_t = sig->challengeP[indexOf(sig->challengeC, params->numOpenedRounds, t)];

            if (P_t != (params->numMPCParties - 1) ) {
                memcpy(sigBytes, sig->proofs[t].aux, params->andSizeBytes);
                sigBytes += params->andSizeBytes;
            }

            memcpy(sigBytes, sig->proofs[t].input, params->stateSizeBytes);
            sigBytes += params->stateSizeBytes;

            memcpy(sigBytes, sig->proofs[t].msgs, params->andSizeBytes);
            sigBytes += params->andSizeBytes;

            memcpy(sigBytes, sig->proofs[t].C, params->digestSizeBytes);
            sigBytes += params->digestSizeBytes;
        }
    }

    return (int)(sigBytes - sigBytesBase);
}

