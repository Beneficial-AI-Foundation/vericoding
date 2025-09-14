

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Sum(N:int) returns (s:int)
  requires N >= 0
  ensures s == N * (N + 1) / 2
// </vc-spec>
// <vc-code>
{
  s := 0;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant s == i * (i + 1) / 2
  {
    i := i + 1;
    s := s + i;
  }
}
// </vc-code>

