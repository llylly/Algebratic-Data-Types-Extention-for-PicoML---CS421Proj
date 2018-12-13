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
MODULE_SOLUTION=solution
MODULE_RUBRIC=rubric

MODULE_LEX=picomllex
MODULE_YACC=picomlparse

OBJLANG=picoml
INTERACTIVE_EXE=$(OBJLANG)Interp

#######################################################################
# DISTFILES define what goes into mpNtest.tgz distributions
#######################################################################

all: $(GRADER_NAME) $(INTERACTIVE_EXE) $(INTERACTIVE_EXE)Sol

$(MPVERSION).pdf: ../$(MPVERSION).tex
	(cd ..; $(LATEX) $(MPVERSION).tex; $(LATEX) $(MPVERSION).tex)
	$(CP) ../$(MPVERSION).pdf .

DISTFILES_SOURCE=pre-rubric.c tests Makefile $(MODULE_COMMON).ml $(INTERACTIVE_EXE).ml $(OBJLANG)parse.mly $(OBJLANG)lex.mll
DISTFILES_OBJECT=$(MODULE_COMMON).cmo $(MODULE_COMMON).cmi $(OBJLANG)parse.cmo $(OBJLANG)parse.cmi $(OBJLANG)lex.cmo $(OBJLANG)lex.cmi $(MODULE_SOLUTION).cmo $(MODULE_SOLUTION).cmi

IMPLEMENTATIONS= $(MODULE_COMMON).cmo $(OBJLANG)parse.cmo $(OBJLANG)lex.cmo $(MPVERSION).cmo $(MODULE_SOLUTION).cmo 

DISTFILES_OTHER=README $(MPVERSION)-skeleton.ml $(MPVERSION).pdf .ocamlinit
DISTFILES=$(DISTFILES_SOURCE) $(DISTFILES_OBJECT) $(DISTFILES_OTHER)

OBJECTS=$(IMPLEMENTATIONS) $(MODULE_RUBRIC).cmo

STUDENT_CLEAN=$(MODULE_RUBRIC).cm? util.o $(GRADER_NAME) \
        $(INTERACTIVE_EXE) $(INTERACTIVE_EXE)Sol $(INTERACTIVE_EXE)*.cm? $(INTERACTIVE_EXE)2* \
		$(MODULE_LEX).cm? $(MODULE_YACC).cm?

$(GRADER_NAME): $(LIBRARY_GRADER) $(OBJECTS)
	$(OCAMLC) -o $(GRADER_NAME) $(LIBRARY_GRADER) $(OBJECTS) 

$(INTERACTIVE_EXE): $(GRADER_NAME) $(INTERACTIVE_EXE).ml
	$(OCAMLC) -c $(INTERACTIVE_EXE).ml
	$(OCAMLC) -o $(INTERACTIVE_EXE) $(IMPLEMENTATIONS) $(INTERACTIVE_EXE).cmo 

$(INTERACTIVE_EXE)Sol: $(GRADER_NAME) $(INTERACTIVE_EXE).ml
	sed 's/Eval_exp/Solution/g' $(INTERACTIVE_EXE).ml > $(INTERACTIVE_EXE)2.ml
	$(OCAMLC) -c $(INTERACTIVE_EXE)2.ml
	$(OCAMLC) -o $(INTERACTIVE_EXE)Sol $(IMPLEMENTATIONS) $(INTERACTIVE_EXE)2.cmo

$(LIBRARY_GRADER):
	$(GMAKE) -C lib
	$(LN) -s lib/util.o .

$(MPVERSION).cmo: $(MPVERSION).ml
	$(OCAMLC) -c -o $(MPVERSION).cmo $(MPVERSION).ml

$(MODULE_LEX).cmo: $(MODULE_LEX).mll
	$(OCAMLLEX) $(MODULE_LEX).mll
	$(OCAMLC) -c $(MODULE_LEX).ml

$(MODULE_YACC).cmo: $(MODULE_YACC).mly
	$(OCAMLYACC) -v $(MODULE_YACC).mly
	$(OCAMLC) -c $(MODULE_YACC).mli
	$(OCAMLC) -c $(MODULE_YACC).ml

########################################################################
# if solution.ml exists, compile it.  otherwise assume solution.cm{o,i}
# exist.
########################################################################
ifeq "$(wildcard $(MODULE_SOLUTION).ml)" "$(MODULE_SOLUTION).ml"
$(MODULE_COMMON).cmo: $(MODULE_COMMON).ml
	$(OCAMLC) -c $(MODULE_COMMON).ml 
$(OBJLANG)parse.cmo: $(OBJLANG)parse.mly
	$(OCAMLYACC) $(OBJLANG)parse.mly
	$(OCAMLC) -c $(OBJLANG)parse.mli
	$(OCAMLC) -c $(OBJLANG)parse.ml

$(OBJLANG)lex.cmo: $(OBJLANG)lex.mll
	$(OCAMLLEX) $(OBJLANG)lex.mll
	$(OCAMLC) -c $(OBJLANG)lex.ml

$(MODULE_SOLUTION).cmo: $(MODULE_SOLUTION).ml
	$(OCAMLC) -c $(MODULE_SOLUTION).ml
endif

$(MODULE_RUBRIC).cmo: $(MODULE_COMMON).cmi pre-$(MODULE_RUBRIC).c tests $(IMPLEMENTATIONS) $(LIBRARY_GRADER)
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
	$(RM) -f $(OBJLANG)lex.ml $(OBJLANG)lex.cm? $(OBJLANG)parse.cm? $(OBJLANG)parse.ml $(OBJLANG)parse.mli $(INTERACTIVE_EXE).cm? $(INTERACTIVE_EXE) $(INTERACTIVE_EXE).cm* $(INTERACTIVE_EXE)Sol* $(MODULE_SOLUTION).cm?
