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

		s1 = RIGHTROTATE(w[i - 2], 17) ^ RIGHTROTATE(w[i - 2], 19)
						^ (w[i - 2] >> 10);


		// uint32_t w16_s0 = w[i - 16] + s0;
		// uint32_t w7_s1 = w[i - 7] + s1;		

		w[i] = w[i - 16] + s0 + w[i - 7] + s1;
		
		// printf("[SHA]  s0[%d] = %d             s1[%d] = %d             w[%d] = %d             w7_s1[%d] = %d\n", i, s0, i, s1, i, w[i], i, w7_s1);
		// printf("[SHA256] w[%d] = %d \n", i, w[i]);
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

		// printf("[SHA256] s1[%d] = %d \n", i, s1);
		// printf("[SHA256] ch[%d] = %d\n", i, CH(e,f,g));
		// printf("[SHA256] h_s1[%d] = %d \n", i, h + s1);
		// printf("[SHA256] ch_k[%d] = %d \n", i, CH(e,f,g) + k[i]);
		// printf("[SHA256] chk_w[%d] = %d \n ", i, CH(e,f,g) + k[i] + w[i]);

		temp1 = h + s1 + CH(e, f, g) + k[i] + w[i];
		// printf("[SHA256] temp1[%d] = %d\n",i, temp1);

		s0 = RIGHTROTATE(a,2) ^ RIGHTROTATE(a, 13) ^ RIGHTROTATE(a, 22);
		// printf("[SHA256] s0[%d] = %d \n", i, s0);

		maj = (a & (b ^ c)) ^ (b & c);
		// printf("[SHA256] maj[%d] = %d   a = %d  b = %d  c = %d\n", i, maj, a, b, c);
		temp2 = s0 + maj;
		// printf("[SHA256] temp2[%d] = %d \n", i, temp2);

		h = g;
		g = f;
		f = e;
		// printf("[SHA256] [%d] h = %d   g = %d   f = %d\n", i, h, g, f);

		e = d + temp1;
		// printf("[SHA256] e[%d] = %d \n", i, e);

		d = c;
		c = b;
		b = a;
		// printf("[SHA256] [%d]  d = %d  c = %d  b = %d\n", i, d, c, b);

		a = temp1 + temp2;
		// printf("[SHA256] a[%d] = %d\n", i, a);   // BUG SUR A[2] != a[2]

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
