

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
  var i := 1;
  while i <= N
    invariant 0 <= N && 1 <= i <= N + 1 && s == (i - 1) * i / 2
  {
    s := s + i;
    i := i + 1;
  }
}
// </vc-code>

