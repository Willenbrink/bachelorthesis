# Trie-based Indexing
Coordinate Indexing (CI), Path Indexing (PI) and Discrimination Nets (DN)

All are based on a trie in which a position + symbol is associated with a set of terms.
The methods differ mostly in the definition of position. Assume a term "f(x,g(y,z,a))" is given. The position of z is:
- <2,2> in CI, second argument of f, second argument of g
- <f,2,g,2> in PI, functions are included
- <f,x,g,y,z> in DN, all preorder symbols are part of the position

A trie simply compactly stores this information, e.g. f(x,g(y)) and f(x,y) share everything except the subtrie g(y) =/= y. Therefore a lookup of (<f,2>,x) or <f,2,x> (when the symbol as appended to the pos) in PI would return both f(x,g(y)) and f(x,y).

Additionally all variables can be replaced by either a common * ignoring all identity or by indexed *_1, *_2 respecting distinct variables but ignoring the actual name.

For coordinate and path indexing retrieval works by collecting the sets for each symbol in the term. These sets are then intersected, i.e. only the terms which match the searched term in every symbol are returned (for identity, small changes allow one to search for generalizations/instances).
Discrimination nets work differently because all relevant information is saved and a single query unambiguously determines a term. (TODO why exactly?)

# Substitution-based Indexing
Abstraction Trees (AT), Substitution Trees (ST)

These are based on a tree in which the path to a leaf describes a series of substitutions whose composition result in the searched term.

ATs start with a term and a list of free variables. Each child of the node are a list of equal length containing the substitution of each variable. E.g. root: f(a,b) [a,b] and child: [g(c),d] would result in a term f(g(c),d), [c,d]. The next child must apparently substitute all variables instead of keeping them constant across multiple substitutions, e.g. [h(c),d] resulting in f(g(h(c)),d) instead of removing d from the free variables in the step before. TODO why?

STs start with only a term. Free variables are no longer explicitly listed. Instead each child contains a mapping of variables to substitutions. As such it is quite similar to and more elegant than ATs. The resulting term is then simply a composition of each substitution.

See https://apps.dtic.mil/dtic/tr/fulltext/u2/a460990.pdf for more information. Also contains algorithms for retrieval and discussion of performance.

# Other methods
Term-table indexing. No papers, no comments, only source code. See term_ord.ML and term_sharing.ML.

Codeword indexing. More or less irrelevant

Context tree indexing. A quick search returned only off-topic results.

FPA indexing is mentionend in [this paper](https://eclass.upatras.gr/modules/document/file.php/CEID1178/%CE%A3%CE%A5%CE%A3%CE%A4%CE%97%CE%9C%CE%91%CE%A4%CE%91%20%CE%91%CE%A0%CE%9F%CE%94%CE%95%CE%99%CE%9E%CE%97%CE%A3%20%CE%98%CE%95%CE%A9%CE%A1%CE%97%CE%9C%CE%91%CE%A4%CE%A9%CE%9D/%CE%A5%CE%9B%CE%99%CE%9A%CE%9F%20%CE%A0%CE%91%CE%A1%CE%91%CE%94%CE%9F%CE%A3%CE%95%CE%A9%CE%9D/McCune1992_Article_ExperimentsWithDiscrimination-.pdf). Essentially a predecessor for CI/PI.

More methods are mentioned in the [wiki article](https://en.wikipedia.org/wiki/Term_indexing), e.g. relational path indexing