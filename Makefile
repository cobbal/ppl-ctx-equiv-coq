EXTRA_DIR:=coqdocjs/extra
COQDOCFLAGS:= \
  --external 'https://www.ps.uni-saarland.de/autosubst/doc/' autosubst \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS

all: coq

auto-subst:
	git clone https://github.com/tebbi/autosubst auto-subst-unpack
	(cd auto-subst-unpack; git checkout coq86-devel; make)
	mv auto-subst-unpack auto-subst

coq: Makefile.coq
	@$(MAKE) -f Makefile.coq

html: Makefile.coq
	@$(MAKE) -f Makefile.coq html
# pandoc --from markdown_github-hard_line_breaks --to html --standalone -o html/index.html < README.md
	cp README.md html
	cp $(EXTRA_DIR)/resources/* html

Makefile.coq: auto-subst Makefile _CoqProject src/*.v
	coq_makefile -f _CoqProject -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f lia.cache
	rm -rf dep-graph
	rm -f src/*.vo src/*.glob src/*.v.d
	rm -f all.pdf

pages: html
	mkdir -p pages
	rm -f pages/*
	cp html/* pages/

remind-me-how-to-commit-to-pages-and-really-I-should-automate-this:
	@echo '(make pages && cd pages && git add *.html *.js *.css *.md && git commit -am "$$(..; git rev-parse HEAD)")'

graph: dep-graph/graph.pdf

dep-graph/graph.pdf: dep-graph/graph.dot
	dot -Tpdf -o $@ $^

dep-graph/graph.dot: dep-graph/graph.dpd
	dpd2dot -o $@ $^

dep-graph/graph.dpd: src/dep.v coq
	mkdir -p dep-graph
	coqc -R ./auto-subst/theories Autosubst -R ./src OpSemProofs src/dep.v

.PHONY: all coq graph html pages remind-me-how-to-commit-to-pages-and-really-I-should-automate-this
