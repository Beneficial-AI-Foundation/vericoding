// For the uniqueness lemma, I need to prove that if both `r1` and `r2` satisfy the sqrt predicate for the same `x`, then `r1 == r2`. This can be proven by contradiction - if `r1 != r2`, then one is larger than the other, leading to a contradiction with the sqrt predicate.

// For the implementation of `mySqrt`, I can use binary search or a simple iterative approach. I'll use an iterative approach that increments from 0 until I find the right value.

// Author: Shaobo He

predicate sqrt(x: int, r: int) {
    r*r <= x && (r+1)*(r+1) > x
}

// <vc-spec>
lemma uniqueSqrt(x: int, r1: int, r2: int)
requires x >= 0 && r1 >= 0 && r2 >= 0;
ensures sqrt(x, r1) && sqrt(x, r2) ==> r1 == r2
{
  if sqrt(x, r1) && sqrt(x, r2) {
    if r1 < r2 {
      assert r1 + 1 <= r2;
      assert (r1 + 1) * (r1 + 1) <= r2 * r2;
      assert (r1 + 1) * (r1 + 1) > x; // from sqrt(x, r1)
      assert r2 * r2 <= x; // from sqrt(x, r2)
      assert false;
    } else if r1 > r2 {
      assert r2 + 1 <= r1;
      assert (r2 + 1) * (r2 + 1) <= r1 * r1;
      assert (r2 + 1) * (r2 + 1) > x; // from sqrt(x, r2)
      assert r1 * r1 <= x; // from sqrt(x, r1)
      assert false;
    }
  }
}

// <vc-helpers>
// </vc-helpers>

method mySqrt(x: int) returns (res: int)
requires 0 <= x;
ensures sqrt(x, res);
// </vc-spec>
// <vc-code>
{
  res := 0;
  while (res + 1) * (res + 1) <= x
    invariant res >= 0
    invariant res * res <= x
  {
    res := res + 1;
  }
}
// </vc-code>