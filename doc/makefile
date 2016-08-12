.PHONY: clean view edit

SRC=	preamble.tex \
	code-list.tex \
	chap-1-foreword.tex \
	chap-2-memcad-intro.tex \
	chap-3-refman.tex \
	chap-appendix.tex \
	manual.tex

manual.pdf: $(SRC)
	pdflatex manual.tex && \
	makeindex commands  && \
	makeindex options   && \
	pdflatex manual.tex

all: manual.pdf

view: manual.pdf
	evince manual.pdf &

clean:
	\rm -f *.aux *.dvi *.idx *.ilg *.ind *.log *.toc *.pdf

edit:
	emacs manual.tex &
