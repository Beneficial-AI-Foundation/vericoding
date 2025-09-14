

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method Sum(N:int) returns (s:int)
  requires N >= 0
  ensures s == N * (N + 1) / 2
// </vc-spec>
// <vc-code>
{
  s := N * (N + 1) / 2;
}
// </vc-code>

