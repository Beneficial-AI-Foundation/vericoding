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


// Question 8 (20 points)
//
// Implement, and have Verus verify, the method Reverse below, which returns a new array
// aRev consisting of the elements of a, but in reverse order.  To create a new 
// array of ints use the Verus command "Vec::with_capacity(...)", where "..." is the number
// of elements in the array.

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn reverse(a: &Vec<i32>) -> (a_rev: Vec<i32>)
    ensures
        a_rev.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] == a_rev[a_rev.len() - i - 1]
// </vc-spec>
// <vc-code>
{
    let mut a_rev = Vec::with_capacity(a.len());
    let mut i = 0;
    
    while i < a.len()
        invariant
            a_rev.len() == i,
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[a.len() - j - 1] == a_rev[j]
        decreases a.len() - i
    {
        a_rev.push(a[a.len() - i - 1]);
        i += 1;
    }
    
    a_rev
}
// </vc-code>

// Question 9 (20 points)
//
// Implement and verify method NoDups, which returns true if and only if there
// are no duplicate elements in array a.  Note that the requires clause allows
// you to assume that a is sorted, and that this precondition is necessary for
// the ensures clause to imply a lack of duplicates.

fn main() {}

}