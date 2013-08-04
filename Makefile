COQ_SRC = type.v tactics.v utils.v coercion.v subst.v unify.v flatten.v good.v co_kind.v \
          dragon.v
COQ_OUTPUT = $(COQ_SRC:%.v=%.vo)
COQ_INCLUDES = $(HOME)/work/etc/coq/tlc $(HOME)/work/etc/coq/cpdt/src
COQ_INCLUDE_SWITCH = $(COQ_INCLUDES:%=-I %) -I .
COQDEP = coq.depend

all : $(COQ_OUTPUT)

.PHONY: clean all
clean:
	rm -f *.vo *.glob $(COQDEP) $(COQ_FILE_MARKER)

$(COQDEP): $(COQ_SRC)
	coqdep $(COQ_INCLUDE_SWITCH) $(COQ_SRC) > $(COQDEP)

ifneq ($(MAKECMDGOALS),clean)
    -include $(COQDEP)
endif

%.vo : %.v
	coqc $(COQ_INCLUDE_SWITCH) $<

