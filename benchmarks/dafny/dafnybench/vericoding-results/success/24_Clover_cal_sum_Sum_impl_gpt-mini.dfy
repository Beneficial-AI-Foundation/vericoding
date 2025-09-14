

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Sum(N:int) returns (s:int)
  requires N >= 0
  ensures s == N * (N + 1) / 2
// </vc-spec>
// <vc-code>
{
  var i := 0;
  s := 0;
  while i < N
    invariant 0 <= i <= N
    invariant s == i * (i + 1) / 2
    decreases N - i
  {
    i := i + 1;
    s := s + i;
  }
}
// </vc-code>

