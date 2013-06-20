all: StickerModule.tex
	pdflatex StickerModule.tex
clean:
	rm -rf *.log *.dvi *.toc *.aux *.ps *~ *.tag
