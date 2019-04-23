.PHONY: coq

MF_COQ = Makefile.coq

build: $(MF_COQ)
	$(MAKE) -f $(MF_COQ)

$(MF_COQ): _CoqProject
	coq_makefile -f _CoqProject -o $(MF_COQ)

