
.PHONY: all build clean

all: report.pdf build

report.pdf: *.tex lib/*.lhs test/*.lhs exec/*.lhs references.bib
	latexmk -pdf report

build:
	stack build

clean:
	stack clean
	rm -f *.aux *.log *.out *.snm *.toc *.vrb *.nav *.synctex.gz *.blg *.bbl *.fdb_latexmk *.fls *.ind *.idx *.ilg *.bcf *.run.xml *.xdv
