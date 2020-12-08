# Tasks
## TODO
* Context genauer anschauen. Evtl RNG-Seed darin speichern?
* Isabelle/Isar Impl. Manual: 0.8 (0.8.2) überfliegen
* Lambda Term Generation Idee: Ohne Probability
  - Höhe -> Index -> State -> (Symbol,Num_Args) (evtl. Path, bisheriger Term)
    Höhe + Index: Ebenenweise und global. D.h. bei Binärbaum in 2./3. Ebene: 1,2,3,4 statt 1,2,1,2
  - Paper für Lambda Term Generators
  - Typkorrektheit erstmal vernachlässigen
  - Wie Application lösen? Also: Funktion hängt von Argumenten ab
* Tests für Path Indexing (als Funktor über NET)
* Implementiere eine andere Indexing Methode (Substitution Trees?)
* net.ML: content = entries?
* Beispiele wo net.ML schlecht funktioniert (net.ML ist nicht HOL?)
    - Überapproximationen bei Lambdas
    - Beta-eta-normal form = Eta-long beta-normal form?
    - Ähnliche Beispiele zu: plus(x,y,150) aus einem Paper
* Beispiele wo pathindexing schlecht funktioniert
    - Kurze Terme: Alle längeren 
    - Konsistente Typen bei Indexing!
* Benchmarks (FOL)
    - DN vs PI vs TT on ground terms (ohne Variablen)
        + TT braucht weniger Steps (da balanciert) aber immer wieder neuer Vergleich (kein prefix sharing)
        + Was zeichnet andere Worst-/Best-Cases aus?
    - DN vs PI in general
* Vergleiche Nutzung von `net.ML`, `item_net.ml`, termtabs (`term_ord.ml`, `term_sharing.ml`) in Taktiken etc.
    - Unterschied zwischen Instanzen von TT
    - Zufällig?
    - Präferenzen?
    - Gründe für Präferenzen?
* Termstruktur ändern für Indextree (Spine representation?)
* `net.ML` umschreiben und Interface anpassen
* Itemnet: Quasi zwei stufiges DN, erst Liste für letzten paar Terme, rest im Netz. Komplex, nicht im Detail anschauen

## Low Priority
* Seven Virtues of STT lesen
* Near-eta conversion in net.ML?
* Isabelle besser herrichten
* Interne Repräsentation von FOL, Quantifiers, Lambdas, Theorems etc. genauer anschauen, print_satement hernehmen?

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
