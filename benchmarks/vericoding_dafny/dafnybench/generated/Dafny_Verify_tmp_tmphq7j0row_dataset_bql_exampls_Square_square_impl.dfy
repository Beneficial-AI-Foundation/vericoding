method square (n: int) returns (r: int)
    requires 0 <= n;
    ensures r == n*n;
// </vc-spec>
// <vc-code>
{
  r := n * n;
}
// </vc-code>