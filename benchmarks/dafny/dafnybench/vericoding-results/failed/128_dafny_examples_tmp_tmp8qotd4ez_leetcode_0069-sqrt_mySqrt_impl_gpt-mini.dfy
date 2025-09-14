// Author: Shaobo He

predicate sqrt(x: int, r: int) {
    r*r <= x && (r+1)*(r+1) > x
}

// <vc-helpers>
lemma IncreaseSquareStrict(res: int)
  requires 0 <= res
  ensures (res + 1) * (res + 1) > res * res
{
  calc {
    (res + 1) * (res + 1);
    == res * res + 2 * res + 1;
    > res * res;
  }
}
// </vc-helpers>

// <vc-spec>
method mySqrt(x: int) returns (res: int)
requires 0 <= x;
ensures sqrt(x, res);
// </vc-spec>
// <vc-code>
{
  res := 0;
  while (res + 1) * (res + 1) <= x
    invariant 0 <= res && res * res <= x
    decreases x - res * res
  {
    IncreaseSquareStrict(res);
    res := res + 1;
  }
}
// </vc-code>

