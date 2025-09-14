//power -- Stephanie Renee McIntyre
//Based on the code used in the course overheads for Fall 2018

//There is no definition for power, so this function will be used for validating that our imperative program is correct.

/* Proof of implied (a): Follows from definition of the power function. */

/* Proof of implied (b): Details left as exercise, but this is relatively simple. */

/* Proof of implied (c): Simple substitution and uses the fact that i=n. */

/* Proof of termination: the loop guard gives us the expression i<n. This is equivalent to n-i>=0.
   Prior to the loop, n>=0 and i=0.
   Each iteration of the loop, i increases by 1 and thus n-i decreases by 1. Thus n-i will eventually reach 0.
   When the n-i=0, n=i and thus the loop guard ends the loop as it is no longer the case that i<n.
   Thus the program terminates.
*/

// <vc-helpers>
lemma PowerMultiplicative(a: int, i: int, n: int)
  requires 0 <= a && 0 <= i && i <= n
  ensures power(a, i) * power(a, n - i) == power(a, n)
  decreases n - i
{
  if i == n {
    assert power(a, n - i) == power(a, 0) == 1;
  } else {
    PowerMultiplicative(a, i + 1, n);
    assert power(a, i) * power(a, n - i) == power(a, i) * a * power(a, n - i - 1);
    assert power(a, i) * a * power(a, n - i - 1) == a * (power(a, i) * power(a, n - i - 1));
    assert a * (power(a, i) * power(a, n - i - 1)) == a * power(a, i + (n - i - 1));
    assert a * power(a, i + (n - i - 1)) == a * power(a, n - 1);
    assert a * power(a, n - 1) == power(a, n);
  }
}
// </vc-helpers>

// <vc-spec>
function power(a: int, n: int): int //function for a to the power of n
  requires 0 <= a && 0 <= n;
  decreases n;{if (n == 0) then 1 else a * power(a, n - 1)}

//Our code from class
method compute_power(a: int, n: int) returns (s: int)
/*Pre-Condition*/   requires n >= 0 && a >= 0;
/*Post-Condition*/  ensures s == power(a,n);
// </vc-spec>
// <vc-code>
{
  s := 1;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant s == power(a, i)
    decreases n - i
  {
    s := s * a;
    i := i + 1;
  }
}
// </vc-code>

