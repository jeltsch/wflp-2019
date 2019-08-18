build_pdfs = isabelle build -o document=pdf -d Paper -d Slides

all:
	$(build_pdfs) Paper Slides
Paper:
	$(build_pdfs) Paper
Slides:
	$(build_pdfs) Slides
.PHONY: all Paper Slides
