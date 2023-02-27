SHELL := /bin/bash

# This variable should be set only inside the Docker container.
ifndef TEXLIVE_CONTAINER

# We are not in the container. Execute the same command inside the
# container.

USER_ID=$(shell id -u)
GROUP_ID=$(shell id -g)
IMAGE_NAME="vakaras/texlive:2021-06-28"

default: thesis.pdf

.cache:
	mkdir -p .cache

shell: | .cache
	sudo docker run --rm -ti \
		--user="$(USER_ID):$(GROUP_ID)" \
		-v "${CURDIR}":/data \
		-v "${CURDIR}"/.cache:/home/developer \
		$(IMAGE_NAME) \
		/bin/bash

%: | .cache
	sudo docker run --rm -ti \
		--user="$(USER_ID):$(GROUP_ID)" \
		-v "${CURDIR}":/data \
		-v "${CURDIR}"/.cache:/home/developer \
		$(IMAGE_NAME) \
		/bin/bash -c "make $@"

else

LATEX = latex
PDFLATEX = xelatex
BIBTEX = bibtex
DVIPS = dvips
DVIPDF = dvipdf
PDFTOEPS = pdftops -eps
PDFTOPS = pdf2ps
EPSTOPDF = epstopdf
FIGTODEV = fig2dev
MPOST = mpost

TEXFILES = $(wildcard *.tex)

.PHONY: default clean

default: thesis.pdf

thesis.pdf: $(TEXFILES)
	$(PDFLATEX) -shell-escape thesis.tex
	$(BIBTEX) thesis
	$(PDFLATEX) -shell-escape thesis.tex
	$(PDFLATEX) -shell-escape thesis.tex

%.pdf: %.svg
	inkscape --file $< --export-pdf=$@

clean:
	rm -rf build/
	rm -f *.aux
	rm -f thesis.aux thesis.bbl thesis.blg thesis.dvi thesis.log thesis.out thesis.pdf thesis.ps thesis.thm thesis.toc texput.log
	rm -rf _minted-thesis/

endif
