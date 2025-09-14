// Author: Shaobo He

predicate sqrt(x: int, r: int) {
    r*r <= x && (r+1)*(r+1) > x
}

// <vc-helpers>
lemma SqrtExists(x: int)
  requires 0 <= x
  ensures exists r: int :: sqrt(x, r)
{
  if x == 0 {
    assert sqrt(0, 0);
  } else {
    var r := 0;
    var rr := 0;
    while rr <= x
      invariant 0 <= r
      invariant rr == r * r
      invariant rr <= x + 2*r + 1
    {
      r := r + 1;
      rr := r * r;
    }
    assert (r-1)*(r-1) <= x;
    assert r*r > x;
    assert sqrt(x, r - 1);
  }
}

lemma SqrtUnique(x: int, r1: int, r2: int)
  requires sqrt(x, r1) && sqrt(x, r2)
  ensures r1 == r2
{
}

lemma SquareNonNegative(r: int)
  ensures r * r >= 0
{
}

lemma MidpointBounds(low: int, high: int)
  requires 0 <= low < high
  ensures low <= (low + high) / 2 < high
{
}

lemma SquareMonotonic(a: int, b: int)
  requires 0 <= a <= b
  ensures a * a <= b * b
{
}
// </vc-helpers>

// <vc-spec>
method mySqrt(x: int) returns (res: int)
requires 0 <= x;
ensures sqrt(x, res);
// </vc-spec>
// <vc-code>
{
  if x == 0 {
    res := 0;
  } else {
    var low := 0;
    var high := x + 1;
    while low + 1 < high
      invariant 0 <= low < high <= x + 1
      invariant low * low <= x
      invariant high * high > x
    {
      var mid := (low + high) / 2;
      assert low <= mid < high;
      if mid * mid <= x {
        low := mid;
        assert low * low <= x;
      } else {
        high := mid;
        assert high * high > x;
      }
    }
    res := low;
    assert res * res <= x;
    assert (res + 1) * (res + 1) > x by {
      assert high == res + 1;
    }
  }
}
// </vc-code>

