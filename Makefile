COQ_SRC = type.v tactics.v utils.v coercion.v ty_kind.v co_kind.v \
          subst.v var.v compose.v unify.v good.v subset.v
COQ_OUTPUT = $(COQ_SRC:%.v=%.vo)
COQ_INCLUDES = $(HOME)/work/etc/coq/tlc
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


