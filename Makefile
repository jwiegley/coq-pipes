MODULES := $(MODULES_NODOC) $(MODULES_DOC)
TEX     := $(MODULES:%=%.v.tex)

VFILES = $(wildcard src/*.v)				\
         $(wildcard src/Pipes/*.v)

VOFILES = $(patsubst %.v,%.vo,$(VFILES))

COQFLAGS = ""

MISSING = find src -name '*.v'						\
		 \(							\
		    ! -name Notes.v					\
		    ! -name CpdtTactics.v				\
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

# ls -1 * | egrep -v '(Utils).hs' | \
#     while read file; do rm -f $$file; done

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Setup
	rm -fr dist .coq-native
	rm -fr .hdevtools.sock *.glob *.d *.vo .*.aux
