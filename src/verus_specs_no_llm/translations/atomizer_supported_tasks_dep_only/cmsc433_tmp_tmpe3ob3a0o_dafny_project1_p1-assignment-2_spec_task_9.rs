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

//ATOM_PLACEHOLDER_ArraySum

// Question 5 (10 points)

// Euclid's algorithm is used to compute the greatest common divisor of two
// positive integers.  If m and n are two such integers, then gcd(m, n) is the
// largest positve integer that evenly divides both m and n, where j evenly divides i
// if and only if i % j == 0 (% is the Dafny mod operator).  Write requires and
// ensures clauses for the method header Euclid below.  Your requires clauses
// should also specify that the first argument is at least as large as the second.
// You do *not* need to implement the method!

//ATOM_PLACEHOLDER_Euclid//ATOM_PLACEHOLDER_IsSorted

// Question 7 (20 points)
//
// Implement, and have Dafny verify, the method IsPrime below, which returns true
// if and only if the given positive integer is prime.

//ATOM_PLACEHOLDER_IsPrime

// Question 8 (20 points)
//
// Implement, and have Dafny verify, the method Reverse below, which returns a new array
// aRev consisting of the elements of a, but in reverse order.  To create a new 
// array of ints use the Dafny command "new int[...]", where "..." is the number
// of elements in the array.

//ATOM_PLACEHOLDER_Reverse

// Question 9 (20 points)
//
// Implement and verify method NoDups, which returns true if and only if there
// are no duplicate elements in array a.  Note that the requires clause allows
// you to assume that a is sorted, and that this precondition is necessary for
// the ensures clause to imply a lack of duplicates.

// SPEC 

// Question 9 (20 points)
//
// Implement and verify method NoDups, which returns true if and only if there
// are no duplicate elements in array a.  Note that the requires clause allows
// you to assume that a is sorted, and that this precondition is necessary for
// the ensures clause to imply a lack of duplicates.

method NoDups (a: Vec<int>) -> (noDups: bool)
    requires and
//,
             clauses
// should also specify that the first argument is at least as large as the second.
// You do *not* need to implement the method!

//ATOM_PLACEHOLDER_Euclid//ATOM_PLACEHOLDER_IsSorted

// Question 7 (20 points)
//
// Implement, and have Dafny verify, the method IsPrime below, which returns true
// if and only if the given positive integer is prime.

//ATOM_PLACEHOLDER_IsPrime

// Question 8 (20 points)
//
// Implement, and have Dafny verify, the method Reverse below, which returns a new array
// aRev consisting of the elements of a, but in reverse order.  To create a new 
// array of ints use the Dafny command "new int[...]", where "..." is the number
// of elements in the array.

//ATOM_PLACEHOLDER_Reverse

// Question 9 (20 points)
//
// Implement and verify method NoDups, which returns true if and only if there
// are no duplicate elements in array a.  Note that the,
             clause allows
// you to assume that a is sorted, and that this precondition is necessary for
// the,
             clause allows
// you to assume that a is sorted, and that this precondition is necessary for
// the,
             forall j : int :: 0 < j < a.len() ==> a[j-1] <= a[j] // a sorted
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

//ATOM_PLACEHOLDER_ArraySum

// Question 5 (10 points)

// Euclid's algorithm is used to compute the greatest common divisor of two
// positive integers.  If m and n are two such integers, then gcd(m,n) is the
// largest positve integer that evenly divides both m and n, where j evenly divides i
// if and only if i % j == 0 (% is the Dafny mod operator).  Write,
            clauses for the method header Euclid below.  Your,
            clause to imply a lack of duplicates.

// SPEC 

// Question 9 (20 points)
//
// Implement and verify method NoDups, which returns true if and only if there
// are no duplicate elements in array a.  Note that the,
            clause to imply a lack of duplicates.

method NoDups (a : array<int>) returns (noDups : bool),
            noDups <==> forall j : int :: 1 <= j < a.len() ==> a[j-1] != a[j]
{
}

}