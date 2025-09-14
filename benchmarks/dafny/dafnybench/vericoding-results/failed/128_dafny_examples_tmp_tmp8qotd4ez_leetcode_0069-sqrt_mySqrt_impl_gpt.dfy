// Author: Shaobo He

predicate sqrt(x: int, r: int) {
    r*r <= x && (r+1)*(r+1) > x
}

// <vc-helpers>
lemma SquareIncrease(r: int)
  requires 0 <= r
  ensures r*r < (r+1)*(r+1)
{
  assert 0 <= 2*r;
  assert 0 < 2*r + 1;
  calc {
    r*r;
    < r*r + (2*r + 1);
    == (r+1)*(r+1);
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
  var r := 0;
  while ((r + 1) * (r + 1) <= x)
    invariant 0 <= r
    invariant r * r <= x
    invariant x - r *
// </vc-code>

