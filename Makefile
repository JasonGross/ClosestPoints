Makefile.coq: _CoqProject
	coq_makefile -f "$<" -o "$@"

-include Makefile.coq
