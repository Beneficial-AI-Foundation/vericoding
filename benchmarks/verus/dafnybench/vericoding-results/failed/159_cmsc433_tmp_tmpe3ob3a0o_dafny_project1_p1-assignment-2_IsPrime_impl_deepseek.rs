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
fn div_lemma(m: int, n: int, d: int, r: int)
    requires
        n > 0,
        d == m / n,
        r == m % n,
    ensures
        m == d * n + r,
        0 <= r < n,
{
}

fn mod_lemma(m: int, n: int, j: int)
    requires
        n > 0,
        j > 0,
        m % j == 0,
    ensures
        (m / j) * j == m,
{
}

proof fn gcd_properties(m: int, n: int, gcd_result: int)
    requires
        m > 0,
        n > 0,
        gcd_result > 0,
    ensures
        m % gcd_result == 0,
        n % gcd_result == 0,
        forall|d: int| d > 0 && m % d == 0 && n % d == 0 ==> d <= gcd_result,
{
}

spec fn sorted_implies_no_duplicates(a: Vec<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a@[i] <= a@[j]
}

spec fn is_prime_spec(m: int) -> bool {
    m > 1 && forall|j: int| 2 <= j < m ==> m % j != 0
}

spec fn array_sum_match(a: Vec<int>, b: Vec<int>, result: Vec<int>) -> bool {
    a.len() == b.len() && a.len() == result.len() &&
    forall|i: int| 0 <= i < a.len() ==> result@[i] == a@[i] + b@[i]
}

spec fn reverse_spec(a: Vec<int>, result: Vec<int>) -> bool {
    a.len() == result.len() &&
    forall|i: int| 0 <= i < a.len() ==> result@[i] == a@[a.len() - 1 - i]
}
// </vc-helpers>

// <vc-spec>
fn is_prime(m: int) -> (is_prime: bool)
    requires m > 0, // m must be greater than 0
    ensures is_prime <==> (m > 1 && forall|j: int| 2 <= j < m ==> #[trigger] (m % j) != 0),
    // ensures states that "is_prime is true iff m > 1 && not divisible by [2, m-1)"
// </vc-spec>
// <vc-code>
{
  if m <= 1 {
    return false;
  }
  
  let mut j: int = 2;
  while j < m
    invariant
      2 <= j <= m,
      forall|k: int| 2 <= k < j ==> m % k != 0,
  {
    if m % j == 0 {
      return false;
    }
    j = j + 1;
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