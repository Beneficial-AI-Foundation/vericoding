/*predicate palindrome<T(==)> (s:seq<T>)
{
    forall i:: 0<=i<|s| ==> s[i] == s[|s|-i-1]
}
*/
// SUM OF A SEQUENCE OF INTEGERS
//ATOM_PLACEHOLDER_sum

/*
//ATOM_PLACEHOLDER_vector_Sum

// Structural Induction on Sequences
//ATOM_PLACEHOLDER_left_sum_Lemma

// MAXIMUM OF A SEQUENCE
// SPEC 

// MAXIMUM OF A SEQUENCE
method maxSeq(v: seq<int>) returns (max:int)
requires |v| >= 1
ensures forall i :: 0 <= i < |v| ==> max >= v[i]
ensures max in v
{
}


// TODO: Hacer
// Derivar formalmente un calculo incremental de j*j*j
//ATOM_PLACEHOLDER_Cubes


// REVERSE OF A SEQUENCE
//ATOM_PLACEHOLDER_reverse

//ATOM_PLACEHOLDER_seq2set


//ATOM_PLACEHOLDER_seq2setRev_Lemma


//ATOM_PLACEHOLDER_concat_seq2set_Lemma


// REVERSE IS ITS OWN INVERSE

//ATOM_PLACEHOLDER_Rev_Lemma//ATOM_PLACEHOLDER_ItsOwnInverse_Lemma

// SCALAR PRODUCT OF TWO VECTORS OF INTEGER
//ATOM_PLACEHOLDER_scalar_product


//ATOM_PLACEHOLDER_scalar_product_Lemma

// MULTISETS

//ATOM_PLACEHOLDER_multiplicity_examples

// REVERSE HAS THE SAME MULTISET 

//ATOM_PLACEHOLDER_seqMultiset_Lemma
*/
//ATOM_PLACEHOLDER_empty_Lemma 
ensures r == []
{
	if r != []	{
	}
}

//ATOM_PLACEHOLDER_elem_Lemma//ATOM_PLACEHOLDER_sumElems_Lemma

