COQMAKEFILE ?= Makefile.coq

all: $(COQMAKEFILE)
	mkdir -p output
	$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE): _CoqProject
	coq_makefile -f _CoqProject -o $(COQMAKEFILE)

clean: $(COQMAKEFILE)
	rm -rf output
	$(MAKE) -f $(COQMAKEFILE) clean
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf
	find . -type f \( -name '*~' -o -name '*.aux' -o -name '.lia.cache' -o -name '.nia.cache' \) -delete

.PHONY: all clean

