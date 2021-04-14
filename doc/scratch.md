# Content of the scratch buffer I accumulated during meetings

TODO
motiv
term index bottleneck for atp, auch itp
atps combine indices ref
atps use x and y etc.
E, spass, vampire, z3
no clear winner
atps 40-50%% in queries
itp eig nicht, user verwenden standard bib index
isabelle, lean, (coq?) jeweils manuals ref
Immer komplexer -> Bessere Datenstrukturen notwendig
immer mehr intern, Contrast zu sledgehammer weil overhead ref
itp / atp Grenze nicht klar, itp immer mehr quasi atp
-> Mehr Auswahl für User, einheitliches Interface

Neuer Term Index
Interface/Framework
Vergleich in ML
Welche Probleme gibts dabei?
- Path Index for FOL
- Evaluation, Vergleich
- Interface
- Was für Anfragen sind überhaupt möglich
- Speccheck überarbeitet, bessere Term Generatoren. Wird nicht im Detail beschrieben. Doku in ref

Abstract ähnlich, term index wichtig. ITP immer mehr automatisieren, Libs immer größer
-> provide better indices
Bisher wenig arbeit, mit dieser Arbeit Framework einführen unter einem Interface. PI FOL vergleich mit DT
Adapting to internal representation

Graphen normalisiert für 5000 Terme
bar graph farblos
%nicht getestet in itp bei anderen arbeiten
related: passt trotz generalisierung
Extension to HOL
Subtree promising
Real world application
Abkürzungen erwähnen
log log
conspicious refer to section...
subcaption -> capiton
termtables vergleich drinnen lassen aber problem erwähnen
the the greppen
abstract + danksagung?
query in net.ml???
\coloneqq usage
Example Environ everywhere?
Groß/Kleinschreibung von Funktionen
biblio checken
Was wird getestet, was sollen die aussagen? Use case nicht klar.
    Eher viel/wenig Prefixsharing mit mehr oder weniger Varianz. Keine Beispiele
Eher weniger als 10 Plots
Zacken überprüfen ob er an der selben Stelle ist
check setbased indexing reference for values instead of terms
Preorder -> preorder
Terms -> terms
Symbol -> symbol
emph at all defn

PLAN
...

Query direkt an Baum zeigen
nicht günstig
Prolog TI Motiv
Regeln mit Attributen

Bsp. bei Implementationsproblemen

Warum das ganze Zeug?

benchmark: adhoc framework, csv export weil query

Bisher im Kernel, jetzt auch in Userspace Term Indexing
Interface verallgemeinern
Wählen je nach Wünschen

Worst Case von DT erwähnen?
Future Work: HOL, was müsste man da genau machen?

https://apps.dtic.mil/dtic/tr/fulltext/u2/a460990.pdf
https://link.springer.com/content/pdf/10.1007%2F3-540-61040-5_16.pdf
https://eclass.upatras.gr/modules/document/file.php/CEID1178/%CE%A3%CE%A5%CE%A3%CE%A4%CE%97%CE%9C%CE%91%CE%A4%CE%91%20%CE%91%CE%A0%CE%9F%CE%94%CE%95%CE%99%CE%9E%CE%97%CE%A3%20%CE%98%CE%95%CE%A9%CE%A1%CE%97%CE%9C%CE%91%CE%A4%CE%A9%CE%9D/%CE%A5%CE%9B%CE%99%CE%9A%CE%9F%20%CE%A0%CE%91%CE%A1%CE%91%CE%94%CE%9F%CE%A3%CE%95%CE%A9%CE%9D/McCune1992_Article_ExperimentsWithDiscrimination-.pdf

https://people.mpi-inf.mpg.de/~hillen/compit/evaluation.pdf

tests on real isabelle theories
design in a way such that other trees can be implemented and tests, e.g. substitution trees.
extension to higher order logic

mention your interface when talking about testing isabelle theories

E
Spass
Vampire
Z3

Isabelle, Lean
(verwenden beide discrimination tries)

values =/= sets of values
need only
focusses -> focuses
references

We plan an “auto Sledgehammer” mode for Isabelle were each goal is auto-matically passed to all 3 ATPs with a low timeout like 5s. The low timeoutavoids the current effect of users going into sleep mode and waiting for thedefault 60s timeout of all ATPs before they reactivate their brain.

