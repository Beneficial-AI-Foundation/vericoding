// Author: Shaobo He

predicate sqrt(x: int, r: int) {
    r*r <= x && (r+1)*(r+1) > x
}

// <vc-helpers>
lemma sqrtUnique(x: int, r1: int, r2: int)
  requires 0 <= x
  requires sqrt(x, r1) && sqrt(x, r2)
  ensures r1 == r2
{
  if r1 < r2 {
    assert (r1+1)*(r1+1) > x;
    assert r2 >= r1 + 1;
    assert r2*r2 >= (r1+1)*(r1+1) > x;
    assert r2*r2 <= x;
    assert false;
  } else if r2 < r1 {
    assert (r2+1)*(r2+1) > x;
    assert r1 >= r2 + 1;
    assert r1*r1 >= (r2+1)*(r2+1) > x;
    assert r1*r1 <= x;
    assert false;
  }
}

lemma sqrtExists(x: int)
  requires 0 <= x
  ensures exists r: int :: sqrt(x, r)
{
  if x == 0 {
    assert sqrt(0, 0);
  } else {
    var r := 0;
    while (r+1)*(r+1) <= x
      invariant 0 <= r
      invariant r*r <= x
    {
      r := r + 1;
    }
    assert sqrt(x, r);
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method mySqrt(x: int) returns (res: int)
requires 0 <= x;
ensures sqrt(x, res);
// </vc-spec>
// </vc-spec>

// <vc-code>
method MySqrt(x: int) returns (res: int)
  requires 0 <= x
  ensures sqrt(x, res)
{
  if x == 0 {
    return 0;
  }
  res := 0;
  while (res+1)*(res+1) <= x
    invariant 0 <= res
    invariant res*res <= x
  {
    res := res + 1;
  }
}
// </vc-code>
