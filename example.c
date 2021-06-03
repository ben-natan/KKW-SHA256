
#include "projet.h"
#include <stdio.h>
#include <memory.h>
#include <inttypes.h>


int picnicExample() {
    unsigned char witness[8] = "abcdefgh";
    int ret = projet_sign(witness);
    return ret;
}

int main() {
    int ret = picnicExample();
    return ret;
}