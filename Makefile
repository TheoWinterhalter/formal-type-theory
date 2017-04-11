default: rules.pdf

src/tt.tex: src/tt.v
	cd ./src && ./coq2latex.py tt.v > tt.tex

rules.pdf: src/rules.tex src/tt.tex
	cd ./src && pdflatex rules.tex
	mv src/rules.pdf .

clean:
	rm -f src/tt.tex
	rm -f rules.pdf
