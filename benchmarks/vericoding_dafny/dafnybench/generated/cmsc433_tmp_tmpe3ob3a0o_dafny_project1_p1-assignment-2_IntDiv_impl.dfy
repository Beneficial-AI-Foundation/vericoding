// Fill in a requires clause that enables Dafny to verify
// method PlusOne



// Question 2 (5 points)
//
// Fill in requires clause(s) that enable(s) Dafny to verify the array bounds
// in method Swap (which swaps elements i and j in array a).


// Question 3 (5 points)
//
// Give ensures clause(s) asserting that d is the result, and r the
// remainder, of dividing m by n.  Your clauses cannot use "/" or "%" (which are
// the Dafny division and mod operators, respectively). By definition, the
// remainder must be non-negative.

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IntDiv (m : int, n : int) returns (d : int, r : int)
    requires n > 0
    ensures m == n * d + r && 0 <= r < n // TODO
// </vc-spec>
// <vc-code>
{
  if m >= 0 {
    d := 0;
    r := m;
    while r >= n
      invariant m == n * d + r
      invariant r >= 0
      decreases r
    {
      d := d + 1;
      r := r - n;
    }
  } else {
    // For negative m, we need to find d and r such that m = n * d + r and 0 <= r < n
    d := 0;
    r := m;
    while r < 0
      invariant m == n * d + r
      invariant r < n
      decreases -r
    {
      d := d - 1;
      r := r + n;
    }
    // At this point r >= 0, but we need to ensure r < n
    while r >= n
      invariant m == n * d + r
      invariant r >= 0
      decreases r
    {
      d := d + 1;
      r := r - n;
    }
  }
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
// if and only if i % j == 0 (% is the Dafny mod operator).  Write requires and
// ensures clauses for the method header Euclid below.  Your requires clauses
// should also specify that the first argument is at least as large as the second.
// You do *not* need to implement the method!


// Question 7 (20 points)
//
// Implement, and have Dafny verify, the method IsPrime below, which returns true
// if and only if the given positive integer is prime.


// Question 8 (20 points)
//
// Implement, and have Dafny verify, the method Reverse below, which returns a new array
// aRev consisting of the elements of a, but in reverse order.  To create a new 
// array of ints use the Dafny command "new int[...]", where "..." is the number
// of elements in the array.


// Question 9 (20 points)
//
// Implement and verify method NoDups, which returns true if and only if there
// are no duplicate elements in array a.  Note that the requires clause allows
// you to assume that a is sorted, and that this precondition is necessary for
// the ensures clause to imply a lack of duplicates.