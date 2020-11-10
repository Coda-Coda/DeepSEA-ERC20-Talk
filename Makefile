%.svg: %.pdf Makefile
	inkscape $< --export-text-to-path --export-plain-svg=$@

%.paths.svg: %.svg Makefile
	inkscape $< --export-text-to-path --export-plain-svg=$@

export COQPATH := $(shell pwd)/coq/

driver := eval $$(opam env) && ./driver.py --template template --mathjax "https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js" talk.rst

# --skip-help
serve:
	$(driver)

docs: talk.rst Makefile
	$(driver) $@
	touch $@/.nojekyll

svgs: breakdowns.svg stdlib.svg breakdowns.paths.svg citations.paths.svg rss.paths.svg stdlib.paths.svg udiv.opt.paths.svg

coq: $(wildcard build/*.v)
	for f in coq/*.v; do coqc -Q coq "" $$f; done

.PHONY: coq
