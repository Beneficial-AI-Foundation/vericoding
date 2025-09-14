// Author: Shaobo He

predicate sqrt(x: int, r: int) {
    r*r <= x && (r+1)*(r+1) > x
}

// <vc-helpers>
predicate sqrt(x: int, r: int) {
    r*r <= x && (r+1)*(r+1) > x
}
// </vc-helpers>

// <vc-spec>
method mySqrt(x: int) returns (res: int)
requires 0 <= x;
ensures sqrt(x, res);
// </vc-spec>
// <vc-code>
{
  var lo := 0;
  var hi := x;
  while lo < hi
    invariant 0 <= lo && lo <= hi && hi <= x
    invariant lo * lo <= x
    invariant forall k : int :: k > hi ==> k * k > x
  {
    var mid := (lo + hi + 1) / 2;
    if mid * mid <= x {
      lo := mid;
    } else {
      hi := mid - 1;
    }
  }
  res := lo;
}
// </vc-code>

