all: coq

auto-subst:
	git clone https://github.com/tebbi/autosubst auto-subst-unpack
	(cd auto-subst-unpack; make)
	mv auto-subst-unpack auto-subst

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

live-html: Makefile.coq html/live.js
	$(MAKE) -f Makefile.coq COQDOCFLAGS="-interpolate -utf8 --no-lib-name" html

Makefile.coq: auto-subst Makefile _CoqProject src/*.v
	coq_makefile -f _CoqProject -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f lia.cache
	rm -rf dep-graph
	rm -f src/dep.vo src/dep.glob
	rm -f html all.pdf

graph: dep-graph/graph.pdf

dep-graph/graph.pdf: dep-graph/graph.dot
	dot -Tpdf -o $@ $^

dep-graph/graph.dot: dep-graph/graph.dpd
	dpd2dot -o $@ $^

dep-graph/graph.dpd: dep.v coq
	mkdir -p dep-graph
	coqc -R ./auto-subst/theories Autosubst -R . OpSemProofs dep.v

.PHONY: all coq graph
