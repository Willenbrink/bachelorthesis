#!/usr/bin/env fish
bibtex main
pdflatex -halt-on-error main.tex
okular ./main.pdf &
inotifywait -m -r --include "\.tex" -e modify . |
    while read path action file # Unnecessary at this time
	  bibtex main
          pdflatex -halt-on-error main.tex
    end
