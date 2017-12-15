MODULES_NODOC	   =
MODULES_PROSE	   =
MODULES_CODE	   = src/Pipes/Internal src/Pipes/Core src/Pipes
MODULES_DOC	   = $(MODULES_PROSE) $(MODULES_CODE)
MODULES		   = $(MODULES_NODOC) $(MODULES_DOC)
TEX		   = $(MODULES:%=%.v.tex)
BIB_FILES	   = coq-pipes.bib
BIBLIOGRAPHIES	   = coq-pipes.pdf
BIBLIOGRAPHIES_bbl = $(BIBLIOGRAPHIES:=.bbl)
BIBLIOGRAPHIES_aux = $(BIBLIOGRAPHIES:=.aux)
LATEX_FILES	   = $(wildcard *.tex src/*.tex src/Pipes/*.tex)
VFILES		   = $(wildcard src/*.v src/Pipes/*.v)
VOFILES		   = $(patsubst %.v,%.vo,$(VFILES))

COQFLAGS = ""

MISSING = find src -name '*.v'						\
		 \(							\
		    ! -name Extract.v					\
		    -print						\
		 \) |							\
		 xargs egrep -i -Hn '(abort|admit|undefined)'     |	\
		       egrep -v 'Definition undefined'

all: $(VOFILES)
	$(MISSING) || exit 0

%.vo: %.v Makefile.coq
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)

%.v.tex: %.v %.glob
	coqdoc --interpolate --latex --utf8 --body-only --light		\
	    --external https://github.com/jwiegley/coq-pipes P		\
	    --external https://github.com/jwiegley/coq-haskell Hask	\
	    -s $*.v -o $*.v.tex

coq-pipes.pdf: coq-pipes.tex $(TEX) coq-pipes.bib src/coqdoc.sty
	mkdir -p latex/Pipes/Internal
	(cd latex/Pipes/Internal; \
	 perl ../../../split.pl ../../../src/Pipes/Internal.v.tex; \
	 for i in *.tex; do perl ../../../fixtex.pl $$i > t; mv t $$i; done)
	perl -i -pe 's/\\~{}/∼/g;' src/*.v.tex src/Pipes/*.v.tex
	perl -i -pe 's/\\\^{}\\coqdocvar{op}/\\textsuperscript{op}/g;' \
	    src/*.v.tex src/Pipes/*.v.tex
	perl -i -pe 's#\\\^{}\\coqexternalref{op}{https://github.com/jwiegley/coq-pipes}{\\coqdocdefinition{op}}#\\textsuperscript{op}#g;' \
	    src/*.v.tex src/Pipes/*.v.tex
	cp -p src/coqdoc.sty .
	perl -i -pe 's/textit/texttt/;' coqdoc.sty
	while (xelatex -shell-escape coq-pipes && \
	    grep -q "Rerun to get" coq-pipes.log ) do true ; \
	done

%.aux: $(LATEX_FILES) $(BIB_FILES)
	xelatex -shell-escape coq-pipes

%.bbl : $(BIB_FILES) $(BIBLIOGRAPHIES_aux)
	bibtex $(@:.bbl=)

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	git clean -dfX
	find src -depth -name .coq-native -exec rm -fr {} \;
	rm -fr latex
