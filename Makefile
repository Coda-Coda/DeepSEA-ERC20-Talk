%.svg: %.pdf Makefile
	inkscape $< --export-text-to-path --export-plain-svg=$@

%.paths.svg: %.svg Makefile
	inkscape $< --export-text-to-path --export-plain-svg=$@

export COQPATH := $(shell pwd)/coq/

# --skip-help
serve:
	./driver.py --template template --mathjax "https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js" talk.rst

svgs: breakdowns.svg stdlib.svg breakdowns.paths.svg citations.paths.svg rss.paths.svg stdlib.paths.svg udiv.opt.paths.svg

coq: $(glob build/*.v)
	for f in coq/*.v; do coqc -Q coq "" $$f; done

coqtop:
	coqtop

.PHONY: coq
