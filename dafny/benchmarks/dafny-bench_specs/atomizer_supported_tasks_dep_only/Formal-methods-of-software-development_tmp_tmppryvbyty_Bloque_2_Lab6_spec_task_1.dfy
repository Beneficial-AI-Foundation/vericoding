/*predicate palindrome<T(==)> (s:seq<T>)
{
    forall i:: 0<=i<|s| ==> s[i] == s[|s|-i-1]
}
*/
// SUM OF A SEQUENCE OF INTEGERS
// ATOM 
// SUM OF A SEQUENCE OF INTEGERS
function sum(v: seq<int>): int 
{
    if v==[] then 0
    else if |v|==1 then v[0]
    else v[0]+sum(v[1..])
}

/*


/*
// SPEC 
method vector_Sum(v:seq<int>) returns (x:int)
ensures x == sum(v) 
{
}


// Structural Induction on Sequences
// ATOM 

// Structural Induction on Sequences
lemma left_sum_Lemma(r:seq<int>, k:int)
requires 0 <= k < |r|
ensures sum(r[..k]) + r[k] == sum(r[..k+1]);
{
    if |r|==1 || k==0{
    }
    else {
        left_sum_Lemma(r[1..], k);

        calc {
            sum(r[..k+1]);
            sum(r[..k]) + [r[k]];
        }
    }
}


// MAXIMUM OF A SEQUENCE
//ATOM_PLACEHOLDER_maxSeq

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

//ATOM_PLACEHOLDER_elem_Lemma// ATOM 
// SUM OF A SEQUENCE OF INTEGERS
function sum(v: seq<int>): int 
{
    if v==[] then 0
    else if |v|==1 then v[0]
    else v[0]+sum(v[1..])
}

/*
Elems_Lemma

