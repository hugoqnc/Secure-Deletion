SHELL := /bin/bash

# This variable should be set only inside the Docker container.
ifndef TEXLIVE_CONTAINER

# We are not in the container. Execute the same command inside the
# container.

USER_ID=$(shell id -u)
GROUP_ID=$(shell id -g)
IMAGE_NAME="vakaras/texlive:2021-06-28"

default: description.pdf

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

default: description.pdf

description.pdf: $(TEXFILES)
	$(PDFLATEX) -shell-escape description.tex
	$(BIBTEX) description
	$(PDFLATEX) -shell-escape description.tex
	$(PDFLATEX) -shell-escape description.tex

%.pdf: %.svg
	inkscape --file $< --export-pdf=$@

clean:
	rm -rf build/
	rm -rf _minted-description
	rm -f *.aux
	rm -f description.aux description.bbl description.blg description.dvi description.log description.out description.pdf description.ps description.thm description.toc

endif
