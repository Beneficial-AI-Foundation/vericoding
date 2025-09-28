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

// <vc-helpers>
proof fn mod_properties(m: int, n: int)
    requires
        n > 0,
    ensures
        m == n * (m / n) + (m % n) && 0 <= m % n < n,
{
    // Built-in properties of division and modulo in Verus
}

proof fn gcd_properties(m: nat, n: nat)
    requires
        m > 0 && n > 0,
    ensures
        m % n == 0 ==> gcd(m, n) == n,
        n % m == 0 ==> gcd(m, n) == m,
{
    // Built-in properties of gcd in Verus
}

spec fn gcd(a: nat, b: nat) -> nat
    recommends
        a > 0 || b > 0,
    decreases
        if a <= b { a } else { b },
{
    if a == 0 {
        b
    } else if b == 0 {
        a
    } else if a <= b {
        gcd(a, b % a)
    } else {
        gcd(a % b, b)
    }
}

spec fn is_prime(n: nat) -> bool {
    // Fixed trigger annotations
    n > 1 && forall|i: nat, j: nat| 
        i > 1 && j > 1 ==> #[trigger] (i * j) != n
}

spec fn reverse<T>(s: Seq<T>) -> Seq<T> {
    Seq::new(s.len(), |i| s[s.len() - 1 - i])
}

spec fn no_dups_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 
        0 <= i < j < s.len() ==> #[trigger] s[i] != #[trigger] s[j]
}
// </vc-helpers>

// <vc-spec>
fn IntDiv(m: int, n: int) -> (ret: (int, int))
    requires n > 0
    ensures m == n * ret.0 + ret.1 && 0 <= ret.1 < n // TODO
// </vc-spec>
// <vc-code>
{
    let mut d = m / n;
    let mut r = m % n;
    proof {
        mod_properties(m, n);
    }
    (d, r)
}
// </vc-code>

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
// array of ints use the Verus command "Vec::new()", where you can build the vector
// with the desired elements.


// Question 9 (20 points)
//
// Implement and verify method NoDups, which returns true if and only if there
// are no duplicate elements in array a.  Note that the requires clause allows
// you to assume that a is sorted, and that this precondition is necessary for
// the ensures clause to imply a lack of duplicates.

fn main() {}

}