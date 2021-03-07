# Gliederung
Introduction: Was hat Isabelle, was bieten wir. 
Hintergrund: TI
DN/PI erklären
State of Affairs QC: nicht verwendet, verbessert
Vergleich
Conclusion

Theorie Praxis splitten
FOL!
Preliminary: FOL in HOL-Setting.
Caveats etc.: Intersection auslagern
Pseudocode, Inferenzregeln. Funktional!
Kombination mit TT und PI in Paper
Term,Value Pair speichern => Wie im Paper
Lookup-Trick erklären: Wert enthalten? Exception!
Ersetzen durch TT weil schneller
Usecase: Resolutionsbeweiser: Literal zu Termlist: Welcher Terme beinhaltet das Literal?
Mehr Prosa, mehr Geschichte. Was sind Probleme, wie kann ich die lösen, nicht so distanziert. Mehr we. But what about variables? etc.

# Tasks
## TODO
* Net_skip beschreiben?
* Mit mathe Notation schreiben, evtl andere Syntax
* Queries Fokus, nicht die Details
* Ground terms useless
* Später: Pathindexing mit Variablennamen
* Tests/Benchmarks als Fokus!
* Vergleiche Nutzung von `net.ML`, `item_net.ml`, termtabs (`term_ord.ml`, `term_sharing.ml`) in Taktiken etc.
    - Unterschied zwischen Instanzen von TT
    - Zufällig?
    - Präferenzen?
    - Gründe für Präferenzen?
* Implementiere eine andere Indexing Methode (Substitution Trees?)
* Beispiele wo net.ML schlecht funktioniert (net.ML ist nicht HOL?)
    - Überapproximationen bei Lambdas
    - Beta-eta-normal form = Eta-long beta-normal form?
    - Ähnliche Beispiele zu: plus(x,y,150) aus einem Paper
* Beispiele wo pathindexing schlecht funktioniert
    - Kurze Terme: Alle Nodes enthalten lange Listen => Intersect wird aufwändiger
    - Konsistente Typen bei Indexing!
* Benchmarks (FOL)
    - DN vs PI vs TT on ground terms (ohne Variablen)
        + TT braucht weniger Steps (da balanciert) aber immer wieder neuer Vergleich (kein prefix sharing)
        + Was zeichnet andere Worst-/Best-Cases aus?
    - DN vs PI in general
* Lösungsansätze für PI identischer Value an mehreren Stellen    
  - terme bei values mit rein
  - termtab zu id mapping
  - term zu id hashing
  - in jeder Node mitabspeichern
  - in der ersten Node mitabspeichern? Komplex!

## Tasks

-4. intersects auf listen
-2. tests sollten mit dem erwarteten uebereinstimmen zB unifiables bei PT sollte nicht essentiell langsamer sein als PI

-1. delete kein value uebergeben
0. Terme zusaetzlich in values rein
  - mit termtables probieren
5. Create benchmarks for Termtabs
3. Thesis schreiben
2. Validierung ob Testergebnisse mit Literaturergebnissen zusammenpassen



4. Beispiele, wo net.ML Überapproximationen lieftert, ob eta-normalform eta-long normal form sein soll, und ob content = entries

6. Check where `net.ml`, `item_net.ml`, and termtabs are used.
  - Is is it just random?
  - Do people prefer one or the other?
  - Do people seem to even have thought about their choice?
7. Discuss: should we provide interfaces that return boolean flags

## Done
- Discrimination Nets: Ueberapproximation
- Path indexing mit selber Signatur wie net.ML
- Reseraching: Generator-based testing in ML-languages: procedure as already given
- probability based approach for term generation
- Paper fuer Lambda Term Generators
- Benchmarks angefangen
- Implentierung mit Referenzen statt Values
- Zeit bei quickCheck reinmachen
- Exception Trace statt reines failen beim Test
- Generatoren mit State fuer Symbole
- Generatoren erzeugen lazy neue Testcases anstatt im vorhinein
- Compiler Type generation klar vom Rest trennen
- Interface wie besprochen + merge
- Intersection optimiert
- Dokumentation
- Termgenerierung abgeschlossen
- Doku

## Themenname
- Techniken zur First-Order Termindizierung in Isabelle/ML
- Techniques for First-Order Term Indexing in Isabelle/ML

## Future Work

1. Instances: the application of Lemma 5.3.3 to this expression could be avoided
by treating subterms that only contain variable arguments as if they were constants.
Moreover, if the term has variable and non-variable arguments,
it suffices to merely consider the non-variable arguments because the basic term sets introduced
for the variables will be supersets of the sets introduced for non- variable arguments.
The definition of the candidate set for instances employs these observations.
2. One could think about creating a minimal path tree storing only values in leafs
3. Are we optimising the queries, e.g. returning empty set if intersecting with an empty set?
4. Discuss: shouldn't we include the names of variables? 
  - It's unclear if it gives any advantages in times of speed due to increased memory consumption. Check out a newer paper. CF Graf
5. Type Konsistenz pruefen. Bisher ist alles untyped

* Ant XML für SpecCheck
* Create benchmarks for item_net???
* Lehmer RNG überarbeiten: Shortlived seeds und split_seeds/sequence implementieren
* Interface-Ideen:
  - Lazy values returnen?
  - Gleich auf Alphaeq, Instanziierung, Generalisations, Unification
  - Operation: Insert only if no generalisation exists
  - Interface mit boolean flags, e.g. generalisation_exists to avoid overhead when immediately discarding result list
* Später: Term generation verbessern
  - Catalan number, Folien ca. 229-237: https://db.in.tum.de/teaching/ws2021/queryopt/slides/chapter3.pdf
  - Prüfer sequenzen

## 30.02
* Bug wenn NoConstraint am Anfang der Liste in intersect
* Pure statt Main importieren

## 23.02
* delete kein value uebergeben
* EQ von insert entfernen bzw. wrappen in convenience functor
* itemtab selbe signatur? Auch vergleichen!
  - Nein, Itemtab braucht von Anfang an alle Terme
* termtabs vergleichen auf lookup
* Terme zusaetzlich in values rein
  - mit termtables probieren
* Benchmark:
    a) vor insert in termtable suchen
    b) vor insert, lookup verwenden
* Create benchmarks for Termtabs

## 16.02
* Fix insert and delete in PI

## 09.02
* v5_10.10? etc. bei Variablennamen
* gen_construction zuerst fixen

## 04.02
* Subtract entfernt, encode aus Modul raus (wohin genau?), merge gelassen
* Intersection optimieren
* Direkt Terme erzeugen mit disjunkten Namen bei Zufallsbaeumen
  - Counter statt zufallsstring
* Path Indexing angefangen zu schreiben
* Lambda Term Generation Dokumentation

## 26.01
* Pathindexing parametrisieren
* Repository version
* Interface:
  - Merge: sehr oft
  - encode_type:
    + Tools/induct.ML
    + HOL/Tools/Lifting/lifting_def_code_dt.ML
  - subtract: gar nicht?
* Memory consumption: Pathindexing besser bei hohem Reuse, schlecht bei Variablen
* Validierung ob Testergebnisse mit Literaturergebnissen zusammenpassen: In etwa
* Memory consumption in QuickCheck: Schwer, wann genau soll getestet werden? Außerdem: memory consumption bestimmen ist langsam

## Bis 19.01
* Exception Trace statt reines failen beim Test
* Zeit bei quickCheck reinmachen
* Compiler Type generation klar vom rest trennen
* Quickcheck Mehr Tests bei Precondition
* Read-only ref? Memory-sharing wird von PolyML gehandelt. Einfach normale Terme nutzen
* `net.ML` umschreiben und Interface anpassen

## Bis 12.01
* Längere Namen bei Tests
* Pathindexing nutzt jetzt 'a ref statt 'a. Bessere performance
* Test für Delete von einem Term der an zwei Stellen gespeichert ist.
* 2 kleine Tests für HOL. PI und DN failen beide. HOL-Terme nicht in Beta-Eta normalform!

## Bis 22.12
* Curried f in term_det
* Testframework als eigenes Repo, Kevin schreiben

## Bis 15.12
* Isabelle/Isar Impl. Manual: 0.8 (0.8.2) überfliegen.
  - Implizites Multithreading reicht
* Context genauer anschauen. Evtl RNG-Seed darin speichern?
  - Anscheinend nicht dafür geeignet. Theoretisch bräuchte man dann nach jedem Aufruf einen Merge und im Endeffekt muss man immer noch den Context/Zustand jeder Funktion übergeben.
* Lambda Term Generation Idee: Ohne Probability
  - Höhe -> Index -> State -> (Symbol,Num_Args) (evtl. Path, bisheriger Term)
    Höhe + Index: Ebenenweise und global. D.h. bei Binärbaum in 2./3. Ebene: 1,2,3,4 statt 1,2,1,2
  - Paper für Lambda Term Generators
  - Typkorrektheit erstmal vernachlässigen
  - Wie Application lösen? Also: Funktion hängt von Argumenten ab
* Tests für Path Indexing (als Funktor über NET)
  - Matching mit Termen testen bei denen man einen Teilbaum durch x ersetzt
* net.ML: content = entries?

## Bis 8.12
* Inferenzregeln auf Papier (nicht Latex) aufschreiben (ala strukturelle Induktion)
* SpecCheck Verwendungen in der Distro? Irgendwo auf Github?
  - Wird weder in der Distro noch auf Github irgendwo verwendet. Das Tool Qcheck für OCaml nutzt auch Kombinatoren für die Generatoren
* Tests für path indexing PROBABILITY-based
  - Generator fuer Variablennamen, Konstantennamen, bound variables
  - Frequenzen von Applications, Abstractions

## Bis 1.12
* Abschlussarbeitanmeldung
* Codestyle
    - Kein empty String als Key
    - Chaining für Options: Siehe Standardbibliothek, Options.map
    - Matching schöner hinschreiben

## Bis 24.11
* TT und fast_term_ord anschauen. B-Baum 3. Ordnung
* Path indexing mit selber Signatur wie net.ML

# Questions and Remarks
## Scratch
* Pathindexing assumes terms as trees with functions above the args. This is opposite from Isabelles term. Does the path structure really make sense?
* Termgeneration ist quasi eine rekursive Intervalteilung. 50 Symbole gesamt: 1-50 bei Toplevel, dann Aufteilung auf Kinder. Bei erstem Kind dann bspw. 1-10. Wie genau soll Gleichverteilung sichergestellt werden?
  - Zufällige Zahlen ziehen, dann auf Interval [0;1] mappen. Jedes Interval hat jetzt eine Prozentzahl der gesamten Symbole zugeordnet.
  - Zufällige Zahlen generieren (Größe der Intervalle). Danach zufällig auf Intervalle mappen. D.h. die 2 Schritte entkoppeln. Nur die Größe der Intervalle kann mit Parametern modifiziert werden.

## Theory
* In [this paper sections 6.1](https://apps.dtic.mil/dtic/tr/fulltext/u2/a460990.pdf) it is mentioned that discrimination nets are the same as tries. Despite this discrimination {net,tree} are apparently used equivalently but distinctly from tries which are used only for the data structure on which DNs are built.
- [ ] Why does DN work so differently from CI/PI? It only contains more context within the keys. Perhaps because the last/rightmost symbol of a term includes all relevant context? Why don't we use only the leafs of the term for PI? I.e. f (g x) y => <f,0,g,0,x> and <f,1,y>
* Because I repeatedly confuse them: A function is applied to an argument, not the other way round.
- [X] Overapproximation == More terms than requested

## Isabelle
- [x] How are FOL terms represented in lambda calculus? What are the implications for Isabelle? In theory FOL == HOL\higher order functions (clue is in the name :P) but for indexing it should be enough to forbid application of higher order lambdas (as we never concern us with the type of a variable). Even then we could allow them but simply return too few terms on lookup (as (\x.(\f.f x) (\i.i)) y == y). E.g. f(x,g(y,z,a)) ==? (\_ _ -> _) x ((\_ _ _ -> _) y z a). That is, the content of a function is irrelevant, only its hash/name is used?

Resolved. Obviously the content of a function is irrelevant as it's not known (variables can also be functions, just a matter of type!). f(x,g(y,z,a) (or rather "f x (g y z a)" as the pair constructors clutter everything up) is represented by
```
Free ("f", "?'a ⇒ ?'b ⇒ ?'c") $ Free ("x", "?'a") $
     (Free ("g", "?'d ⇒ ?'e ⇒ ?'f ⇒ ?'b") $ Free ("y", "?'d") $ Free ("z", "?'e") $
       Free ("a", "?'f"))
```
See the cookbook for more information (p.25). Higher order functions should be fairly obvious to recognize in code (apply argument to value => argument is also a function => HOL)

- [ ] What is the significance of Var vs Free? net.ml only consists of Application, Variables and Atoms. See Cookbook p.37

- [x] How should currying be handled? Is f(x,y) preferred to f x y? => Basically we don't care. f(x,y) = f $ (pair (x,y)) instead of f $ x $ y.

* Eta-normalform in Isabelle is the usual Eta-normalform with all variables/abstractions added as seen in unify.ML eta_norm. This is in contrast to [this article](https://en.wikipedia.org/wiki/Lambda_calculus_definition#Normalization)? We also have eta-long beta-normal form in envir.ML (which apparently does what the name suggest: beta-contract, eta-extend).

* Terms are structured with $ as parents instead of functions and arg lists. I.e. ($) (($) f x) y instead of f [x,y]. Therefore terms must be restructured before building the key for PI (either separately or implicitly in key_of_term)

* !DON'T! use Xtab.map_entry as it fails silently when the key is not present.

## Net.ML
### Beware of optimisations!

- [x] What is implemented in net.ml? It implies discrimination nets but function and variables names are completely disregarded. Apparently it's a first order DN. Whenever higher order terms (functions/variables) are encountered everything below that point is returned.

- [ ] Why is the type of the actual key used in every function exposed as "key list". Shouldn't this be hidden by the interface? "VarK $ X" discards X (see key_of_term). As the type is exposed, a user could construct an arbitrary key list. Instead the key list could be replaced by a tree (e.g. tree = Comb of (tree * tree) | CombVar (no child necessary) | Atom)
