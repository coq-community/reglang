all: Makefile.coq
	+$(MAKE) -f Makefile.coq all

html: Makefile.coq
	+$(MAKE) -f Makefile.coq html

install: Makefile.coq
	+$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	+$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: all html gallinahtml clean install
