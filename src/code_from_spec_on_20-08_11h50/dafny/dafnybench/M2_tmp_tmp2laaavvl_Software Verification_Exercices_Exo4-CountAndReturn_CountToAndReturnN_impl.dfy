method CountToAndReturnN(n: int) returns (r: int)
    requires n >= 0
    ensures r == n
// </vc-spec>
// <vc-code>
{
  r := 0;
  while r < n
    invariant 0 <= r <= n
  {
    r := r + 1;
  }
}
// </vc-code>