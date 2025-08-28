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
lemma power_lemma(a: int, n: int, i: int, result: int)
  requires n >= 0 && a >= 0 && 0 <= i <= n
  requires result == power(a, i)
  ensures a * result == power(a, i + 1)
{
  if i == 0 {
    assert power(a, 1) == a * power(a, 0);
    assert power(a, 0) == 1;
    assert a * result == a * 1 == a == power(a, 1);
  } else {
    assert power(a, i + 1) == a * power(a, i);
    assert result == power(a, i);
    assert a * result == a * power(a, i) == power(a, i + 1);
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
function power(a: int, n: int): int //function for a to the power of n
  requires 0 <= a && 0 <= n;
  decreases n;{if (n == 0) then 1 else a * power(a, n - 1)}

//Our code from class
method compute_power(a: int, n: int) returns (s: int)
/*Pre-Condition*/   requires n >= 0 && a >= 0;
/*Post-Condition*/  ensures s == power(a,n);
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var i: int := 0;
  s := 1;
  
  while i < n
    invariant 0 <= i <= n
    invariant s == power(a, i)
    decreases n - i
  {
    power_lemma(a, n, i, s);
    s := a * s;
    i := i + 1;
  }
}
// </vc-code>
