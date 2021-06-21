// https://github.com/Sobuno/ZKBoo/blob/master/MPC_SHA256/MPC_SHA256.c
// https://fr.wikipedia.org/wiki/SHA-2 Algorithme SHA256
// Il le fait pour un seul bloc (N=1)

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include "sha256.h"


#define CH(e,f,g) ((e & f) ^ ((~e) & g))

static void printMaskedKey(uint32_t* maskedKey) {
    for (int i = 0; i < 16; i++) {
        printf("%d", maskedKey[i]);
        fflush(stdout);
    }
}

int sha256(unsigned char* result, int numBits) {
    uint32_t _hA[8] = { 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
		0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 };

	if (numBits > 447) {
		printf("Input too long, aborting!");
		return -1;
	}
	int chars = numBits >> 3;
	unsigned char* chunk = calloc(64, 1); //512 bits
	memcpy(chunk, "abcdefgh", chars);
	chunk[chars] = 0x80;
	//Last 8 chars used for storing length of input without padding, in big-endian.
	//Since we only care for one block, we are safe with just using last 9 bits and 0'ing the rest

	//chunk[60] = numBits >> 24;
	//chunk[61] = numBits >> 16;
	chunk[62] = numBits >> 8;
	chunk[63] = numBits;

	printf("[SHA256] : \n");
	printMaskedKey((uint32_t*)chunk);
	printf("\n");

	uint32_t w[64];
	int i;
	for (i = 0; i < 16; i++) {
		w[i] = (chunk[i * 4] << 24) | (chunk[i * 4 + 1] << 16)
						| (chunk[i * 4 + 2] << 8) | chunk[i * 4 + 3];
		// printf("[SHA256] w[%d] = %d \n", i, w[i]);
	}

	uint32_t s0, s1;
	for (i = 16; i < 64; i++) {
		s0 = RIGHTROTATE(w[i - 15], 7) ^ RIGHTROTATE(w[i - 15], 18)
						^ (w[i - 15] >> 3);

		// printf("[SHA256] s0[%d] = %d \n",i, s0);

		s1 = RIGHTROTATE(w[i - 2], 17) ^ RIGHTROTATE(w[i - 2], 19)
						^ (w[i - 2] >> 10);


		uint32_t w16_s0 = w[i - 16] + s0;
		printf("[SHA256] w16_s0[%d] = %d \n", i, w16_s0);

		w[i] = w[i - 16] + s0 + w[i - 7] + s1;
		
	}

	uint32_t a, b, c, d, e, f, g, h, temp1, temp2, maj;
	a = _hA[0];
	b = _hA[1];
	c = _hA[2];
	d = _hA[3];
	e = _hA[4];
	f = _hA[5];
	g = _hA[6];
	h = _hA[7];

	for (i = 0; i < 64; i++) {
		s1 = RIGHTROTATE(e,6) ^ RIGHTROTATE(e, 11) ^ RIGHTROTATE(e, 25);

		temp1 = h + s1 + CH(e, f, g) + k[i] + w[i];
		s0 = RIGHTROTATE(a,2) ^ RIGHTROTATE(a, 13) ^ RIGHTROTATE(a, 22);


		maj = (a & (b ^ c)) ^ (b & c);
		temp2 = s0 + maj;


		h = g;
		g = f;
		f = e;
		e = d + temp1;
		d = c;
		c = b;
		b = a;
		a = temp1 + temp2;

	}
	// taille a = 32 bits
	_hA[0] += a;
	_hA[1] += b;
	_hA[2] += c;
	_hA[3] += d;
	_hA[4] += e;
	_hA[5] += f;
	_hA[6] += g;
	_hA[7] += h;

	for (i = 0; i < 8; i++) {
		result[i * 4] = (_hA[i] >> 24);
		result[i * 4 + 1] = (_hA[i] >> 16);
		result[i * 4 + 2] = (_hA[i] >> 8);
		result[i * 4 + 3] = _hA[i];
	}

	
	return 0;
}
