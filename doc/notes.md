# Tasks
## Primary
- [x] Investigate termtables, why/how do they use order?
- [x] Implement path indexing
- [ ] Implement another indexing method
- [ ] Write tests
- [ ] Create benchmarks
- [ ] Modify termstructure for indextree?
- [ ] Understand net.ml in detail (match, unif)

## Secondary
- [ ] Read Seven Virtues of STT
- [ ] Investigate representation: FOL, quantifiers, lambdas, theorems. Use print_statement?
- [ ] Near-eta conversion? What is the beta-eta normalform?

# Questions and Remarks
## Theory
* In [this paper sections 6.1](https://apps.dtic.mil/dtic/tr/fulltext/u2/a460990.pdf) it is mentioned that discrimination nets are the same as tries. Despite this discrimination {net,tree} are apparently used equivalently but distinctly from tries which are used only for the data structure on which DNs are built.
- [ ] Why does DN work so differently from CI/PI? It only contains more context within the keys. Perhaps because the last/rightmost symbol of a term includes all relevant context? Why don't we use only the leafs of the term for PI? I.e. f (g x) y => <f,0,g,0,x> and <f,1,y>
* Because I repeatedly confuse them: A function is applied to an argument, not the other way round.
- [ ] Overapproximation == More terms than requested?

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

* Terms are structured with $ as parents instead of functions and arg lists. I.e. ($) (($) f x) y instead of f [x,y]. Therefore terms must be restructured before building the key for PI (either separately or implicitly in key_of_term)

* !DON'T! use Xtab.map_entry as it fails silently when the key is not present.

## Net.ML
### Beware of optimisations!

- [ ] What is implemented in net.ml? It implies discrimination nets but function and variables names are completely disregarded.

- [ ] Why is the type of the actual key used in every function exposed as "key list". Shouldn't this be hidden by the interface? "VarK $ X" discards X (see key_of_term). As the type is exposed, a user could construct an arbitrary key list. Instead the key list could be replaced by a tree (e.g. tree = Comb of (tree * tree) | CombVar (no child necessary) | Atom)
