%.svg: %.pdf Makefile
	inkscape $< --export-text-to-path --export-plain-svg=$@

%.paths.svg: %.svg Makefile
	inkscape $< --export-text-to-path --export-plain-svg=$@

export COQPATH := $(shell pwd)/contracts/

driver = ./driver.py --template template --mathjax "https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js" slides.rst

# --skip-help
serve-%:
	$(call driver,$*)

docs: slides.rst Makefile
	$(driver) $@
	touch $@/.nojekyll

svgs: breakdowns.svg stdlib.svg breakdowns.paths.svg citations.paths.svg rss.paths.svg stdlib.paths.svg udiv.opt.paths.svg

.PHONY: coq docs
