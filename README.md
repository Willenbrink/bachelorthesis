# Bachelorthesis
My Bachelor's thesis about the implementation of path indexing in Isabelle/ML, including a unified interface for term indices and a testing framework.

## Abstract
In recent years, increasingly powerful proof automation has been introduced to interactive theorem provers such as Isabelle.This automation necessitates efficient data structures to index and query sets of terms.So-called term indices provide queries for retrieving variants, instances, generalisations and unifiables of a given term.Two indexing techniques, path indexing and discrimination tree indexing are reviewed.We implement path indexing for first-order terms in Isabelle/ML and adapt it to the more general term indexing interface defined in Isabelle/ML.We further define a unified interface for the path index and the previously implemented discrimination tree index, thereby clearing the way for the implementation of additional term indices in the future.Lastly, we evaluate the performance of path indexing in relation to discrimination tree indexing.

## Contents
* doc: Some notes written for myself
* spec_check: The testing framework used. See also the mirror at https://github.com/kappelmann/SpecCheck
* src: The code of the thesis. Test.thy links everything, pathX and net.ML are the term indices, term_index.ML the interface.
* test_data: The data used for the plots of the thesis. See also Test.thy for the commands used.
* thesis: The Bachelor's thesis, i.e. the PDF and its Latex sources

## Contact
Sebastian Willenbrink
Email: sebastian.willenbrink@tum.de
