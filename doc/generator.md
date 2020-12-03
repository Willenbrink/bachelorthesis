# Information on Generators
## FOL-Term Generator
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
