method Max(a: int, b: int) returns (c: int)
    ensures c >= a && c >= b && (c == a || c == b)
// </vc-spec>
// <vc-code>
{
  if a >= b {
    c := a;
  } else {
    c := b;
  }
}
// </vc-code>