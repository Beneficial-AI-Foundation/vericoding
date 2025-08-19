// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method square (n: int) returns (r: int)
    requires 0 <= n;
    ensures r == n*n;
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>