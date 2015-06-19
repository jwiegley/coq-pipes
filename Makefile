VFILES = $(wildcard src/*.v)				\
         $(wildcard src/Pipes/*.v)

VOFILES = $(patsubst %.v,%.vo,$(VFILES))

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
	@$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)

Makefile.coq: _CoqProject
	@coq_makefile -f _CoqProject -o $@
	@perl -i fixmake.pl $@

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -fr Makefile.coq Setup dist .coq-native
	rm -fr .hdevtools.sock *.glob *.d *.vo .*.aux
	(cd src; rm -fr .hdevtools.sock *.glob *.d *.vo .*.aux)
	(cd src/Pipes; rm -fr .hdevtools.sock *.glob *.d *.vo .*.aux)
