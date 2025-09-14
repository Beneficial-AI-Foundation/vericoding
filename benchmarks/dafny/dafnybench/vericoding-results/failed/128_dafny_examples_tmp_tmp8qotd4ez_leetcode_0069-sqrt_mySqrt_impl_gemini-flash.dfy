// Author: Shaobo He

predicate sqrt(x: int, r: int) {
    r*r <= x && (r+1)*(r+1) > x
}

// <vc-helpers>
predicate Sqrt(x: int, r: int) {
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
  var res_local := 0;
  while (res_local + 1) * (res_local + 1) <= x
    invariant 0 <= res_local
    invariant res_local * res_local <= x
    decreases x - res_local * res_local
  {
    res_local := res_local + 1;
  }
  return res_local;
}
// </vc-code>

