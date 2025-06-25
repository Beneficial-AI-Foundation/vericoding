// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn Swap(which swaps elements i and j in array a).

//ATOM_PLACEHOLDER_Swap

// Question 3 (5 points)
//
// Give ensures clause(s) asserting that d is the result, and r the
// remainder, of dividing m by n.  Your clauses cannot use "/" or "%" (which are
// the Dafny division and mod operators, respectively). By definition, the
// remainder must be non-negative.

// SPEC 

// Question 3 (5 points)
//
// Give ensures clause(s) asserting that d is the result, and r the
// remainder, of dividing m by n.  Your clauses cannot use "/" or "%" (which are
// the Dafny division and mod operators, respectively). By definition, the
// remainder must be non-negative.

method IntDiv (m: int, n: int) -> (d: int, r: int)
    requires
        n > 0
    ensures
        clause(s) asserting that d is the result, && r the
// remainder, of dividing m by n.  Your clauses cannot use "/" || "%" (which are
// the Dafny division && mod operators, respectively). By definition, the
// remainder must be non-negative.

// SPEC 

// Question 3 (5 points)
//
// Give,
        clause(s) asserting that d is the result, && r the
// remainder, of dividing m by n.  Your clauses cannot use "/" || "%" (which are
// the Dafny division && mod operators, respectively). By definition, the
// remainder must be non-negative.

method IntDiv (m : int, n : int) returns (d : int, r : int),
        m == n * d + r && 0 <= r < n // TODO
{
    return (0, 0);
}

}