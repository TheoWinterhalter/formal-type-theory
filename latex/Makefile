PDFLATEX=pdflatex
COQ2LATEX=./coq2latex.py
MAIN=rules.tex
MAINPARANOID=rulesParanoid.tex

mathpartir.sty:
	./getmathpartir.py

tt.tex: ../src/tt.v ./coq2latex.py
	$(COQ2LATEX) ../src/tt.v

rules.pdf: tt.tex rules.tex mathpartir.sty
	$(PDFLATEX) $(MAIN)
	$(PDFLATEX) $(MAIN)

rulesParanoid.pdf: tt.tex rulesParanoid.tex mathpartir.sty
	$(PDFLATEX) $(MAINPARANOID)
	$(PDFLATEX) $(MAINPARANOID)

clean:
	/bin/rm -f tt.tex *.aux *.log *.pdf
