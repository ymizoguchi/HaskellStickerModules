all: figm1.pdf figmp.pdf
figm1.pdf: figm1.dot
	dot -Tpdf figm1.dot -o figm1.pdf
figmp.pdf: figmp.dot
	dot -Tpdf figmp.dot -o figmp.pdf
clean:
	rm -f *.pbm *.ps *~ *.bmc *.pdf *.eps



