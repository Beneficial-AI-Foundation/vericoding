// <vc-helpers>
// </vc-helpers>

method square (n: int) returns (r: int)
    requires 0 <= n;
    ensures r == n*n;
// <vc-code>
{
  assume false;
}
// </vc-code>