MPVERSION=eval_exp
STUDENTSRC=$(MPVERSION).ml
MODULE_COMMON=common

OCAMLC=ocamlc
OCAMLLEX=ocamllex
OCAMLYACC=ocamlyacc
GMAKE=make
RM=rm
CP=cp
LN=ln
MV=mv
TAR=tar
GZIP=gzip
MKDIR=mkdir
LATEX=pdflatex

GRADER_NAME=grader

LIBRARY_GRADER=lib/grader.cma
MODULE_STUDENT=student
MODULE_RUBRIC=rubric

MODULE_LEX=picomllex
MODULE_YACC=picomlparse
MODULE_TYPEINFERENCER=type_inferencer
MODULE_VALUES=values

OBJLANG=picoml
INTERACTIVE_EXE=$(OBJLANG)Interp

TESTGEN_EXE=genTest

#######################################################################
# DISTFILES define what goes into mpNtest.tgz distributions
#######################################################################

all: $(GRADER_NAME) $(INTERACTIVE_EXE) $(TESTGEN_EXE)

$(MPVERSION).pdf: ../$(MPVERSION).tex
	(cd ..; $(LATEX) $(MPVERSION).tex; $(LATEX) $(MPVERSION).tex)
	$(CP) ../$(MPVERSION).pdf .

DISTFILES_SOURCE=pre-rubric.c proj_tests Makefile $(MODULE_COMMON).ml $(INTERACTIVE_EXE).ml $(OBJLANG)parse.mly $(OBJLANG)lex.mll
DISTFILES_OBJECT=$(MODULE_COMMON).cmo $(MODULE_COMMON).cmi $(OBJLANG)parse.cmo $(OBJLANG)parse.cmi $(OBJLANG)lex.cmo $(OBJLANG)lex.cmi

IMPLEMENTATIONS= $(MODULE_COMMON).cmo $(MODULE_TYPEINFERENCER).cmo $(MODULE_VALUES).cmo $(OBJLANG)parse.cmo $(OBJLANG)lex.cmo $(MPVERSION).cmo

DISTFILES_OTHER=README .ocamlinit
DISTFILES=$(DISTFILES_SOURCE) $(DISTFILES_OBJECT) $(DISTFILES_OTHER)

OBJECTS=$(IMPLEMENTATIONS) $(MODULE_RUBRIC).cmo

STUDENT_CLEAN=$(MODULE_RUBRIC).cm? util.o $(GRADER_NAME) \
        $(INTERACTIVE_EXE) $(INTERACTIVE_EXE)*.cm? $(INTERACTIVE_EXE)2* \
		$(MODULE_LEX).cm? $(MODULE_YACC).cm? \
		$(MODULE_COMMON).cm? $(MPVERSION).cm? \
		$(MODULE_TYPEINFERENCER).cm? $(MODULE_VALUES).cm? \
		$(MODULE_YACC).output

$(GRADER_NAME): $(LIBRARY_GRADER) $(OBJECTS)
	$(OCAMLC) -o $(GRADER_NAME) $(LIBRARY_GRADER) $(OBJECTS) 

$(INTERACTIVE_EXE): $(GRADER_NAME) $(INTERACTIVE_EXE).ml
	$(OCAMLC) -c $(INTERACTIVE_EXE).ml
	$(OCAMLC) -o $(INTERACTIVE_EXE) $(IMPLEMENTATIONS) $(INTERACTIVE_EXE).cmo 

$(TESTGEN_EXE): $(TESTGEN_EXE).ml
	$(OCAMLC) -c $(TESTGEN_EXE).ml
	$(OCAMLC) -o $(TESTGEN_EXE) $(IMPLEMENTATIONS) $(TESTGEN_EXE).cmo 

$(LIBRARY_GRADER):
	$(GMAKE) -C lib
	$(LN) -s lib/util.o .

$(MPVERSION).cmo: $(MPVERSION).ml
	$(OCAMLC) -c -o $(MPVERSION).cmo $(MPVERSION).ml

$(MODULE_COMMON).cmo: $(MODULE_COMMON).ml
	$(OCAMLC) -c -o $(MODULE_COMMON).cmo $(MODULE_COMMON).ml

$(MODULE_TYPEINFERENCER).cmo: $(MODULE_TYPEINFERENCER).ml
	$(OCAMLC) -c -o $(MODULE_TYPEINFERENCER).cmo $(MODULE_TYPEINFERENCER).ml

$(MODULE_VALUES).cmo: $(MODULE_VALUES).ml
	$(OCAMLC) -c -o $(MODULE_VALUES).cmo $(MODULE_VALUES).ml

$(MODULE_LEX).cmo: $(MODULE_LEX).mll
	$(OCAMLLEX) $(MODULE_LEX).mll
	$(OCAMLC) -c $(MODULE_LEX).ml

$(MODULE_YACC).cmo: $(MODULE_YACC).mly
	$(OCAMLYACC) -v $(MODULE_YACC).mly
	$(OCAMLC) -c $(MODULE_YACC).mli
	$(OCAMLC) -c $(MODULE_YACC).ml

$(MODULE_RUBRIC).cmo: $(MODULE_COMMON).cmi pre-$(MODULE_RUBRIC).c proj_tests $(IMPLEMENTATIONS) $(LIBRARY_GRADER)
	gcc -E pre-$(MODULE_RUBRIC).c | grep -E -v "#" > $(MODULE_RUBRIC).ml
	$(OCAMLC) -c -I lib $(MODULE_RUBRIC).ml

clean:
	$(GMAKE) -C lib clean
	$(RM) -f $(STUDENT_CLEAN)

##########################################################################
#these targets are used by staff
##########################################################################

TESTNAME=$(MPVERSION)

dist: $(GRADER_NAME) $(DISTFILES)
	$(RM) -rf $(TESTNAME)
	$(MKDIR) $(TESTNAME)
	$(MKDIR) $(TESTNAME)/lib
	$(CP) lib/Makefile lib/*.ml $(TESTNAME)/lib
	$(CP) $(DISTFILES) $(TESTNAME)
	$(TAR) cpf $(TESTNAME).tar $(TESTNAME)
	$(RM) -rf $(TESTNAME)
	$(GZIP) -9 $(TESTNAME).tar

#if you are a student, do not make dist-clean.  it will delete
#your copy of solution.cmo and you will need to download a new
#copy.
dist-clean: clean
	$(RM) -f $(DISTFILES_OBJECT) $(MODULE_COMMON).cm? $(MODULE_RUBRIC).ml 
	$(RM) -f $(OBJLANG)lex.ml $(OBJLANG)lex.cm? $(OBJLANG)parse.cm? $(OBJLANG)parse.ml $(OBJLANG)parse.mli $(INTERACTIVE_EXE).cm? $(INTERACTIVE_EXE) $(INTERACTIVE_EXE).cm*

