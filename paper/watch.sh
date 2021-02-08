#!/usr/bin/env fish
okular ./main.pdf &
inotifywait -m -r --include "\.tex" -e modify . |
    while read path action file # Unnecessary at this time
          pdflatex -halt-on-error main.tex
    end
