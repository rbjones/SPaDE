####################################################################
#	
#	makefile for SPaDE/dk
#
######################################################################

# suffixes known
.SUFFIXES: .db .doc .pdf .ldd .log .lot .md .sh .pp .tex .tch

# default make target.  displays a list of more useful targets

default:
	@echo " "
	@echo "make -f rbj.mkf pdf      - build database; typeset documents as PDF files"
	@echo "make -f rbj.mkf bld      - just build database"
	@echo "You may need "." in your path to make pdf or doc."

vars:
	@echo MDS: $(MDS)

######################################################################
#
#	Makefile Definitions
#
######################################################################

# Because we use the ProofPower specification source files and are
# using utf8 documents, we need the pp repo in place with branch utf8.

PPHOME=~/git/pp
SPCDIR=$(PPHOME)/src/hol
COMDIR=../common
PPCHARSET=utf8
PPSVF=utf8svf
PRODNAME=dk

PARENTDBNAME=hol
DKDBNAME=dkdb

dkdb.ldd:
	pp_make_database -f -p $(PARENTDBNAME) $(DKDBNAME)
	touch dkdb.ldd

# The documents

SPCPPS=spc001.pp spc002.pp spc003.pp spc004.pp spc005.pp
THPPS=$(SPCPPS:.pp=.th.pp)
PPS=$(SPCPPS)
PPSMLS=$(PPS:.pp=.sml)
PPLDDS=$(PPSMLS:.sml=.ldd)
COMDIRCPY=list_na.sml list_wa.sml

$(SPCPPS): %: $(SPCDIR)/%
	cp $(SPCDIR)/$@ .

$(COMDIRCPY): %: $(COMDIR)/%
	cp $(COMDIR)/$@ .

DKMDS=dk001.md
MDS=$(DKMDS)
MDSMLS=$(MDS:.md=.sml)
MDTEXS=$(MDS:.md=.tex)
THTEXS=$(THPPS:.pp=.th.tex)

SMLS=$(PPSMLS) $(MDSMLS)
LDDS=$(SMLS:.sml=.ldd) dkdb.ldd

thpps: $(THPPS)

bld: $(LDDS)

all: bld thpps

# Theories and Documents ##############################################
#
# This set of dependencies tells which theories are created by (and
# listed in) which documents, and conversely, which tex files depend on
# module builds.
#
######################################################################

dk001.th.pp: dk001.ldd

######################################################################
#
# Dependencies - determining the order of compilation
#
######################################################################

spc001.ldd:dkdb.ldd
spc002.ldd:spc001.ldd
spc003.ldd:spc002.ldd
spc004.ldd:spc003.ldd
spc005.ldd:spc004.ldd

dk001.ldd:spc005.ldd

# some variables and rules concerning document preparation

$(PDFFILES):

SPCTHS=spc001.th spc002.th spc003.th spc004.th spc005.th
DKTHS=dk001.th

######################################################################
#
#	Building the documents
#
######################################################################

doc_theories.tex: $(THTEXS)
	cat $(THTEXS) >| doc_theories.tex

pdf: $(PDFFILES)

#####################################################################
#
#	Tidying Up
#
######################################################################

clean:
	rm -f $(HOLTEXS) $(SMLFILES) $(LDDFILES)
	rm -f *.aux *.bbl *.blg *.err *.idx *.log *.lot *.out *.sid *-e \
	*.thna.pp *.sml *.toc *.th.pp *.stats.doc *.stats.tex t000abs.tex \
	doc_theories.tex \\#*\\#

######################################################################
#
#	Generic Rules
#
######################################################################

$(PPLDDS): %.ldd: %.sml
	@rm -f $@ $*.err 2>/dev/null
	@echo "Compiling (code)" $<
	@PPCHARSET=utf8 pp -d $(DKDBNAME) -f $< >$*.err
	@mv $*.err $@

$(THPPS): %.th.pp: list_wa.sml
	@rm -f $@ $*.err 2>/dev/null
	@echo "Listing hol theory: " $*
	@pp_list -d $(DKDBNAME) -i list_wa.sml $* >$*.err
	sed -e 's/val it = (): unit//' $*.err >$@

$(PPSMLS): %.sml : %.pp
	ppsml -f $(PPSVF) $*

$(MDSMLS):%.sml: %.md
	pandoc yourfile.md --lua-filter=extract_code.lua -t markdown > $@

$(MDTEXS): %.tex: %.md
	pandoc -s --toc --toc-depth=2 --template=ppdoc.tex --pdf-engine=xelatex \
	--metadata-file=ppdoc.yaml --metadata title="$*" $* > $@

$(THTEXS): %.tex: %.th.pp
	pptex -K $*

# .md files

$(): %.tex: %.md
	pptex -K -k minkeys $*

$(PDFFILES): %.pdf: %.pp
	TEXINPUTS=.:$(PPHOME)/tex: \
	BSTINPUTS=.:$(PPHOME)/tex: \
	BIBINPUTS=.:$(PPHOME)/tex: \
	PATH=.:$(PATH) pppdf -f $(PPSVF) $*
