
#include "projet.h"
#include <stdio.h>
#include <memory.h>
#include <inttypes.h>


int picnicExample() {

    // witness = "abcdefgh" avec padding et length
    uint32_t witness[16];

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

    int ret = projet_sign_and_verify(witness);
    return ret;
}

int main() {
    int ret = picnicExample();
    return ret;
}