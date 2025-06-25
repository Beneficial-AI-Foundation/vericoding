// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Swap(which swaps elements i and j in array a).

//ATOM_PLACEHOLDER_Swap

// Question 3 (5 points)
//
// Give ensures clause(s) asserting that d is the result, and r the
// remainder, of dividing m by n.  Your clauses cannot use "/" or "%" (which are
// the Dafny division and mod operators, respectively). By definition, the
// remainder must be non-negative.

//ATOM_PLACEHOLDER_IntDiv

// Question 4 (5 points)
//
// Give ensures clause(s) asserting that the return value has the same
// length as array a and contains as its elements the sum of the
// corresponding elements in arrays a and b.

// SPEC 

// Question 4 (5 points)
//
// Give ensures clause(s) asserting that the return value has the same
// length as array a and contains as its elements the sum of the
// corresponding elements in arrays a and b.

method ArraySum (a: Vec<int>, b: Vec<int>) -> (c: Vec<int>)
    requires a.len() == b.len()
    ensures clause(s) asserting that d is the result, and r the
// remainder, of dividing m by n.  Your clauses cannot use "/" or "%" (which are
// the Dafny division and mod operators, respectively). By definition, the
// remainder must be non-negative.

//ATOM_PLACEHOLDER_IntDiv

// Question 4 (5 points)
//
// Give,
            clause(s) asserting that the return value has the same
// length as array a and contains as its elements the sum of the
// corresponding elements in arrays a and b.

// SPEC 

// Question 4 (5 points)
//
// Give,
            clause(s) asserting that the return value has the same
// length as array a and contains as its elements the sum of the
// corresponding elements in arrays a and b.

method ArraySum (a : array<int>, b : array<int>) returns (c : array<int>),
            c.len() == a.len() and 
        forall i : int :: 0 <= i < c.len() ==> c[i] == a[i] + b[i] // TODO
{
}

}