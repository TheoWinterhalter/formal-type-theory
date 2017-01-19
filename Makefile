default: rules.pdf

formalization/ptt.tex: formalization/ptt.v
	cd ./formalization && ./coq2latex.py ptt.v > ptt.tex

formalization/ett.tex: formalization/ett.v
	cd ./formalization && ./coq2latex.py ett.v > ett.tex

rules.pdf: formalization/rules.tex formalization/ptt.v formalization/ett.v
	cd ./formalization && pdflatex rules.tex
	mv formalization/rules.pdf .
