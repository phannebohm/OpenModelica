# Makefile generated by OpenModelica
# Platform: linux64

# Simulations use -O3 by default
CC=gcc
CXX=g++
LINK=gcc -shared
EXEEXT=
DLLEXT=.so
CFLAGS_BASED_ON_INIT_FILE=
# define OMC_CFLAGS_OPTIMIZATION env variable to your desired optimization level to override this
OMC_CFLAGS_OPTIMIZATION=-Os
DEBUG_FLAGS=$(OMC_CFLAGS_OPTIMIZATION)
CFLAGS=$(CFLAGS_BASED_ON_INIT_FILE) $(DEBUG_FLAGS) -fPIC -falign-functions -mfpmath=sse -fno-dollars-in-identifiers -Wno-parentheses-equality ${MODELICAUSERCFLAGS}
CPPFLAGS= -I"/home/linus/OpenModelica/build/bin/../include/omc/c" -I"/home/linus/OpenModelica/build/bin/../include" -I. -DOPENMODELICA_XML_FROM_FILE_AT_RUNTIME -DOMC_MODEL_PREFIX=multary_simplification -DOMC_NUM_MIXED_SYSTEMS=0 -DOMC_NUM_LINEAR_SYSTEMS=0 -DOMC_NUM_NONLINEAR_SYSTEMS=0 -DOMC_NDELAY_EXPRESSIONS=0 -DOMC_NVAR_STRING=0
# define OMC_LDFLAGS_LINK_TYPE env variable to "static" to override this
OMC_LDFLAGS_LINK_TYPE=dynamic
RUNTIME_LIBS= -Wl,--no-as-needed -Wl,--disable-new-dtags -lSimulationRuntimeC  -L/usr/lib/x86_64-linux-gnu -llapack -lblas    -lm -lomcgc -lpthread -rdynamic -Wl,--no-undefined
LDFLAGS=-L"/home/linus/OpenModelica/build/bin/../lib/x86_64-linux-gnu/omc" -L"/home/linus/OpenModelica/build/bin/../lib" -Wl,-rpath,"/home/linus/OpenModelica/build/bin/../lib/x86_64-linux-gnu/omc" -Wl,-rpath,"/home/linus/OpenModelica/build/bin/../lib"   $(RUNTIME_LIBS)
DIREXTRA=
MAINFILE=multary_simplification.c
MAINOBJ=multary_simplification.o
CFILES=multary_simplification_functions.c multary_simplification_records.c \
multary_simplification_01exo.c multary_simplification_02nls.c multary_simplification_03lsy.c multary_simplification_04set.c multary_simplification_05evt.c multary_simplification_06inz.c multary_simplification_07dly.c \
multary_simplification_08bnd.c multary_simplification_09alg.c multary_simplification_10asr.c multary_simplification_11mix.c multary_simplification_12jac.c multary_simplification_13opt.c multary_simplification_14lnz.c \
multary_simplification_15syn.c multary_simplification_16dae.c multary_simplification_17inl.c multary_simplification_18spd.c

OFILES=$(CFILES:.c=.o)
GENERATEDFILES=$(MAINFILE) multary_simplification.makefile multary_simplification_literals.h multary_simplification_functions.h $(CFILES)

.PHONY: omc_main_target clean bundle

# This is to make sure that multary_simplification_*.c are always compiled.
.PHONY: $(CFILES)

omc_main_target: $(MAINOBJ) multary_simplification_functions.h multary_simplification_literals.h $(OFILES)
	$(CC) -I. -o multary_simplification$(EXEEXT) $(MAINOBJ) $(OFILES) $(CPPFLAGS) $(DIREXTRA)   $(CFLAGS) $(CPPFLAGS) $(LDFLAGS)
clean:
	@rm -f multary_simplification_records.o $(MAINOBJ)

bundle:
	@tar -cvf multary_simplification_Files.tar $(GENERATEDFILES)