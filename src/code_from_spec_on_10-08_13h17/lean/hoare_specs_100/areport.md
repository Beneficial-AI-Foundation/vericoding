# Report about the 100 NumpyHoareTriple 

## Wrong definitions
- Unnecessary use of sorry
- Vector.mk expects an Array not a List (fixed by adding array.mk)
## Wrong proofs
- No mathlib imports despite the use of `type*` and `lemma`. But also conflicted with the use of the same variable names from libraries. 
- Non used LLM helper functions [e.g `arange` : arange_helper on the other hand `vector_get_ofFn` is an LLM helper that is thoroughly used ] 
- Unnecessary wrong LLM helper and extra arguments and tactics 


# Specifics

## arange: 
- We find that the definition of arange is not correct. In fact, it is not using the `stop` parameter and asking for a new n. 


