# Makefile for building the CHDKR paper
# This Makefile compiles the paper from Markdown to LaTeX and then to PDF.
# Ensure you have pandoc and pdflatex installed.

MDFILES=PhilosophicalPreliminaries.md
MDTEXFILES=$(MDFILES:.md=.tex)
PDFS=chdkrpaper.pdf
PDFTEXFILES=$(PDFS:.pdf=.tex)

$(MDTEXFILES):%.tex :%.md
	pandoc $< -o $@

$(PDFS):%.pdf : %.tex
	pdflatex $*
	-bibtex $*
	pdflatex $*
	pdflatex $*

chdkrpaper.pdf: chdkrpaper.tex PhilosophicalPreliminaries.tex

all: $(PDFS)
