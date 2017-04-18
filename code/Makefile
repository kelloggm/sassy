OCB_FLAGS = -libs unix -use-ocamlfind -pkgs Z3 -Is Imp/extract,Imp/ml
OCB_FLAGS := -use-menhir -yaccflags --explain $(OCB_FLAGS)

default: Z3Sample.native Imp.native

Z3Sample.native:
	ocamlbuild $(OCB_FLAGS) Z3Sample/Z3Sample.native

Imp.native: proof
	ocamlbuild $(OCB_FLAGS) Imp/ml/Imp.native 

Imp.d.byte: proof
	ocamlbuild $(OCB_FLAGS) Imp/ml/Imp.d.byte

proof: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

test: Imp.native
	./Imp/test/regression/test.sh
	./Imp/test/bounded/test.sh -2 2

clean-coq: Makefile.coq
	rm -f Imp/extract/*
	$(MAKE) -f Makefile.coq clean
	rm Makefile.coq
	find . -name '.*.aux' -delete

clean-ml:
	ocamlbuild -clean

clean: clean-coq clean-ml

clean-test:
	rm -f Imp/test/regression/*.imp.input
	rm -f Imp/test/regression/*.imp.result
	rm -f Imp/test/bounded/TESTIMP.*

cleaner: clean clean-test
	rm -f _CoqProject

.PHONY: proof test clean-coq clean-ml clean clean-test cleaner
