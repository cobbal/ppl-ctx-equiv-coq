.PHONY: all

all: coq

auto-subst:
	git clone https://github.com/tebbi/autosubst auto-subst-unpack
	(cd auto-subst-unpack; make)
	mv auto-subst-unpack auto-subst

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: auto-subst Makefile _CoqProject *.v
	coq_makefile -f _CoqProject -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
