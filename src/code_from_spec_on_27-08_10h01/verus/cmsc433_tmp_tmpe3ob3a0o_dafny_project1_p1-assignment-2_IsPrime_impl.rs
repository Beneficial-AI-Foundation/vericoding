use vstd::prelude::*;

verus! {

// ASSIGNMENT P1
// CMSC 433 FALL 2023
// PERFECT SCORE:  100 POINTS
//
// This assignment contains nine questions, each of which involves writing Verus
// code. You should include your solutions in a single Verus file and submit it using
// Gradescope.
//
// Revision history
//
// 2023-09-22 2:50 pm   Fixed typo in Problem 3.


// Question 1 (5 points)
//
// Fill in a requires clause that enables Verus to verify
// method PlusOne



// Question 2 (5 points)
//
// Fill in requires clause(s) that enable(s) Verus to verify the array bounds
// in method Swap (which swaps elements i and j in array a).


// Question 3 (5 points)
//
// Give ensures clause(s) asserting that d is the result, and r the
// remainder, of dividing m by n.  Your clauses cannot use "/" or "%" (which are
// the Verus division and mod operators, respectively). By definition, the
// remainder must be non-negative.


// Question 4 (5 points)
//
// Give ensures clause(s) asserting that the return value has the same
// length as array a and contains as its elements the sum of the
// corresponding elements in arrays a and b.


// Question 5 (10 points)

// Euclid's algorithm is used to compute the greatest common divisor of two
// positive integers.  If m and n are two such integers, then gcd(m,n) is the
// largest positve integer that evenly divides both m and n, where j evenly divides i
// if and only if i % j == 0 (% is the Verus mod operator).  Write requires and
// ensures clauses for the method header Euclid below.  Your requires clauses
// should also specify that the first argument is at least as large as the second.
// You do *not* need to implement the method!


// Question 7 (20 points)
//
// Implement, and have Verus verify, the method IsPrime below, which returns true
// if and only if the given positive integer is prime.

// <vc-helpers>
spec fn has_no_divisors_in_range(m: int, start: int, end: int) -> bool {
    forall|j: int| start <= j < end ==> #[trigger] (m % j) != 0
}

proof fn divisor_check_extends(m: int, start: int, mid: int, end: int)
    requires 
        start <= mid <= end,
        has_no_divisors_in_range(m, start, mid),
        has_no_divisors_in_range(m, mid, end)
    ensures has_no_divisors_in_range(m, start, end)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn is_prime(m: int) -> (is_prime: bool)
    requires m > 0, // m must be greater than 0
    ensures is_prime <==> (m > 1 && forall|j: int| 2 <= j < m ==> #[trigger] (m % j) != 0),
    // ensures states that "is_prime is true iff m > 1 && not divisible by [2, m-1)"
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if m <= 1 {
        return false;
    }
    
    if m == 2 {
        return true;
    }
    
    let mut i: int = 2;
    while i < m
        invariant 
            2 <= i <= m,
            has_no_divisors_in_range(m, 2, i)
        decreases m - i
    {
        if m % i == 0 {
            return false;
        }
        i = i + 1;
    }
    
    proof {
        assert(has_no_divisors_in_range(m, 2, m));
    }
    
    true
}
// </vc-code>

// Question 8 (20 points)
//
// Implement, and have Verus verify, the method Reverse below, which returns a new array
// aRev consisting of the elements of a, but in reverse order.  To create a new 
// array of ints use the Verus command "Vec::new()", where the vector can be built
// with the appropriate number of elements.


// Question 9 (20 points)
//
// Implement and verify method NoDups, which returns true if and only if there
// are no duplicate elements in array a.  Note that the requires clause allows
// you to assume that a is sorted, and that this precondition is necessary for
// the ensures clause to imply a lack of duplicates.

fn main() {}

}