CC = gcc
WARNING_FLAGS=-Wall -Wextra -Werror -Wshadow
CFLAGS= -O0 -g -march=native $(WARNING_FLAGS) -std=gnu99 -D__LINUX__ -D__X64__ -I./sha3
NISTKATFLAGS = -Wno-sign-compare -Wno-unused-but-set-variable -Wno-unused-parameter -Wno-unused-result
SHA3LIB=libshake.a
SHA3_PATH=sha3
LDFLAGS= $(SHA3_PATH)/$(SHA3LIB) 


SOURCES= picnic3_impl.c projet.c sha256.c
PICNIC_OBJECTS= picnic3_impl.o projet.o sha256.o hash.o picnic_types.o tree.o
PICNIC_LIB= libpicnic.a
EXECUTABLE_EXAMPLE=example

all: $(SHA3LIB) $(SOURCES) $(PICNIC_LIB) $(EXECUTABLE_EXAMPLE) $(EXECUTABLE_TESTVECTORS) $(EXECUTABLE_UNITTEST) $(EXECUTABLE_KATSTEST)  $(EXECUTABLE_TREETEST) 

$(SHA3LIB):
		$(MAKE) -C $(SHA3_PATH) 

# debug build
debug: CFLAGS = $(CFLAGS_DEBUG)
debug: all

$(EXECUTABLE_EXAMPLE): $(EXECUTABLE_EXAMPLE).c $(PICNIC_LIB)
	    $(CC) $(@).c $(CFLAGS) $(PICNIC_LIB) -o $@ $(LDFLAGS) 


.c.o: 
	    $(CC) -c $(CFLAGS) $< -o $@

$(PICNIC_LIB): $(PICNIC_OBJECTS)
	ar rcs $@ $^

clean:
	    rm *.o 2>/dev/null || true
	    rm *.exe 2>/dev/null || true
	    rm $(EXECUTABLE_EXAMPLE) 2>/dev/null || true
		rm $(PICNIC_LIB) 2>/dev/null || true
		$(MAKE) -C $(SHA3_PATH) clean

