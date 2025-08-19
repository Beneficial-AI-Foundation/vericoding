//IMPL 

// Question 3 (5 points)
//
// Give ensures clause(s) asserting that d is the result, and r the
// remainder, of dividing m by n. Your clauses cannot use "/" or "%" (which are
// the Dafny division and mod operators, respectively). By definition, the
// remainder must be non-negative.

method IntDiv (m : int, n : int) returns (d : int, r : int)
  requires n > 0
  ensures m == n * d + r && 0 <= r < n // TODO
{
  if m >= 0 {
    d := 0;
    r := m;
    while r >= n
      invariant m == n * d + r
      invariant r >= 0
    {
      d := d + 1;
      r := r - n;
    }
  } else {
    d := 0;
    r := m;
    while r < 0
      invariant m == n * d + r
      invariant r < n
    {
      d := d - 1;
      r := r + n;
    }
  }
}