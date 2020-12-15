# Term generation
## Original thoughts on FOL-Term Generator
FOL-Terms consist of 2 distinct components regarding the structure: Symbols and Applications.
The symbols can be one of Bound, Const, Var, Free but this selection can be made after a structure has been generated.
Therefore the generator should be separated into two main functions: 1. Generate functions 2. Generate symbols
To simplify the implementation the functions should be generated in the form: symbol * term list and only later transformed into Isabelle's representation.

The parameters governing the structure are:
- Exact number of symbols
- Average number of arguments: An average of 1 results in a list
- Balancing, i.e. how deep the trees a and b in f(a,b) are in relation to each other

[Random recursive trees](https://en.wikipedia.org/wiki/Random_recursive_tree) appear to solve the problem quite nicely. The number of symbols can be regulated by aborting the generation once functions+symbols > num symbols. A +1 error occurs because an insertion of a symbol may also generate a function. This is acceptable as it is imprecise either way. Average number of arguments may be problematic but can likely be solved by skewing the probability towards already existing functions. Balancing will also be problematic but may not be necessary at all?

An alternative is the [prüfer sequence/code](https://en.wikipedia.org/wiki/Pr%C3%BCfer_sequence) which transforms a sequence of integers into a tree. It seems that it is less straightforward to modify the average number of arguments.

## Random generation
Two distinct steps: Generation of structure and mapping of values
### Structure
1. Generate number of children based on avg and num_sym available
2. Use Bound (num_children) as function symbol
3. Distribute num_sym across children 
4. Recursively continue
### Mapping
Replace every found Bound by either a random function or random constant (as in: takes no argument), depending on the number of arguments

## Deterministic
Generate a tree by using a "fold" with signature "term_det : (int * int * 'a -> term * int * 'a) -> 'a -> term" and usage "term f init_state" where "f height index state" returns a function and its number of arguments together with an updated state.
Alternative int * int can be replaced by a (term * int) list representing the function-symbol and the index of the argument in which we currently are. This is equivalent to the path in path indexing.

## Approaches from papers
http://publications.lib.chalmers.se/records/fulltext/157525.pdf
1.1 Term generators: It is difficult to obtain a reasonable distribution on untyped lambda terms.
5.5, 5.6: TODO
2.3: TODO
Goes into detail on the typing of random terms, the possibility of typing etc. Promising
http://ceur-ws.org/Vol-1433/tc_12.pdf
3.1: TODO
Prolog based, looks relatively simple but incomprehensible due to Prolog. Revisit once Prolog has been introduced in AI lecture
http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.95.2624&rep=rep1&type=pdf
3.2: Generates terms by counting all possible options and selecting one at random. Guaranteed uniform distribution but incredibly performance intensive
3.3: Adds contexts which are basically holes. Could be useful but seems to simplistic for actual applications (because now we have to generate contexts)
http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.193.9697&rep=rep1&type=pdf
Uses Boltzmann-sampling, results in prohibitive performance costs once unary height (= # of nestes lambdas) is larger. 8 is fast, 125 fails on terms larger than 200 symbols (>1 day).
Refers to recursive generation from this paper but I can't find a mention of the recursive method (besides: generate root with distribution, recursively generate the roots subtrees etc.): https://lara.epfl.ch/w/_media/calculus-random.pdf
https://www.cs.tufts.edu/~nr/cs257/archive/john-hughes/quick.pdf
Quickcheck from Haskell generates functions by transformation: Gen (a -> b) == a -> Gen b, that is: a must be able to modify a generator for type b. This is in most cases done by "variant : int -> 'a gen -> 'a gen" which modifies a generator and then converting a to either an int or int list. E.g. bool => variant 0/1 and for lists "coarbitrary (x::xs) = variant 1 o coarbitrary x o coarbitrary xs", i.e. applying the variants from the rest of the list, the first element and variant 1 for good measure. Seemingly, no good distribution is achieved (e.g. for the lists: for all non-empty lists there are repeated applications of variant 1. Unless variant 0 == variant 1 o variant 1 this results in a low probability for variant 0 and it's right out impossible for variant 0 to be combined with other variants)
