# pp2lp paper — LPAR-26.  Build with lualatex (unicode-math) + biber.
MAIN := pp2lp

.PHONY: all watch clean count results

all: $(MAIN).pdf

# Regenerate results-data.tex from lp/bench/results/*.json (single source of
# truth for the benchmark numbers).  No-op when the JSON is absent.
results:
	python3 results-data.py

$(MAIN).pdf: $(wildcard *.tex) $(MAIN).bib
	-python3 results-data.py
	latexmk -lualatex -interaction=nonstopmode -halt-on-error $(MAIN).tex

watch:
	latexmk -lualatex -pvc $(MAIN).tex

clean:
	latexmk -C
	rm -f $(MAIN).bbl $(MAIN).run.xml *.bcf

# Rough page/word count of the body (excludes refs).
count: $(MAIN).pdf
	@pdfinfo $(MAIN).pdf 2>/dev/null | grep Pages || true
