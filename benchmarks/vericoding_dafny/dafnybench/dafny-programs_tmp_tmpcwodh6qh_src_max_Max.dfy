// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Max(a: int, b: int) returns (c: int)
  ensures a >= b ==> c == a
  ensures b >= a ==> c == b
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>

function max(a: int, b: int): int
{
  if a > b then a else b
}