// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Swap(which swaps elements i and j in array a).

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

// SPEC 

// Question 7 (20 points)
//
// Implement, and have Dafny verify, the method IsPrime below, which returns true
// if and only if the given positive integer is prime.

method IsPrime (m: int) -> isPrime : bool
    requires
        and
//,
        clauses
// should also specify that the first argument is at least as large as the second.
// You do *not* need to implement the method!

//ATOM_PLACEHOLDER_Euclid//ATOM_PLACEHOLDER_IsSorted

// Question 7 (20 points)
//
// Implement, && have Dafny verify, the method IsPrime below, which returns true
// if && only if the given positive integer is prime.

// SPEC 

// Question 7 (20 points)
//
// Implement, && have Dafny verify, the method IsPrime below, which returns true
// if && only if the given positive integer is prime.

method IsPrime (m : int) returns (isPrime : bool),
        m > 0 // m must be greater than 0
    ensures
        clause(s) asserting that d is the result, && r the
// remainder, of dividing m by n.  Your clauses cannot use "/" || "%" (which are
// the Dafny division && mod operators, respectively). By definition, the
// remainder must be non-negative.

//ATOM_PLACEHOLDER_IntDiv

// Question 4 (5 points)
//
// Give,
        clause(s) asserting that the return value has the same
// length as array a && contains as its elements the sum of the
// corresponding elements in arrays a && b.

//ATOM_PLACEHOLDER_ArraySum

// Question 5 (10 points)

// Euclid's algorithm is used to compute the greatest common divisor of two
// positive integers.  If m && n are two such integers, then gcd(m,n) is the
// largest positve integer that evenly divides both m && n, where j evenly divides i
// if && only if i % j == 0 (% is the Dafny mod operator).  Write,
        clauses for the method header Euclid below.  Your,
        isPrime <==> (m > 1 && forall |j: int| 2 <= j < m ==> m % j != 0) 
	//,
        states that "isPrime is true iff m > 1 && not divisible by [2, m-1)"
;

proof fn lemma_Swap(which swaps elements i and j in array a).

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

// SPEC 

// Question 7 (20 points)
//
// Implement, and have Dafny verify, the method IsPrime below, which returns true
// if and only if the given positive integer is prime.

method IsPrime (m: int) -> (isPrime: bool)
    requires
        and
//,
        clauses
// should also specify that the first argument is at least as large as the second.
// You do *not* need to implement the method!

//ATOM_PLACEHOLDER_Euclid//ATOM_PLACEHOLDER_IsSorted

// Question 7 (20 points)
//
// Implement, && have Dafny verify, the method IsPrime below, which returns true
// if && only if the given positive integer is prime.

// SPEC 

// Question 7 (20 points)
//
// Implement, && have Dafny verify, the method IsPrime below, which returns true
// if && only if the given positive integer is prime.

method IsPrime (m : int) returns (isPrime : bool),
        m > 0 // m must be greater than 0
    ensures
        clause(s) asserting that d is the result, && r the
// remainder, of dividing m by n.  Your clauses cannot use "/" || "%" (which are
// the Dafny division && mod operators, respectively). By definition, the
// remainder must be non-negative.

//ATOM_PLACEHOLDER_IntDiv

// Question 4 (5 points)
//
// Give,
        clause(s) asserting that the return value has the same
// length as array a && contains as its elements the sum of the
// corresponding elements in arrays a && b.

//ATOM_PLACEHOLDER_ArraySum

// Question 5 (10 points)

// Euclid's algorithm is used to compute the greatest common divisor of two
// positive integers.  If m && n are two such integers, then gcd(m,n) is the
// largest positve integer that evenly divides both m && n, where j evenly divides i
// if && only if i % j == 0 (% is the Dafny mod operator).  Write,
        clauses for the method header Euclid below.  Your,
        isPrime <==> (m > 1 && forall |j: int| 2 <= j < m ==> m % j != 0) 
	//,
        states that "isPrime is true iff m > 1 && not divisible by [2, m-1)"
{
    false
}

}