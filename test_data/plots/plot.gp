set datafile columnheaders
set key autotitle columnheader
set xtics rotate by -45 offset 0,-1
set logscale y 10

do for [i=4:15] {
#do for [i=20:21] { #Insert/Delete
   #set term qt i
   set terminal epslatex
   set output "graph1.tex"
   plot 'test6_mod.txt' in i u 0:1:xticlabels(5) w linespoint,\
        '' in i u 2 w linespoint,\
        '' in i u 3 w linespoint,\
        '' in i u 4 w linespoint
}
pause -1

# PI PITT Generalisations HV
# Unifiables auch. Siehe Plot 10

#([Test "Q: generalisations of existing term", Index "PITT", Gen "HV",
#  Size "S 30-R 1000"],
