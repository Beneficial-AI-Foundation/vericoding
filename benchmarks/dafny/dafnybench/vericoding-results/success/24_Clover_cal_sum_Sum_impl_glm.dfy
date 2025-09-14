

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
  var sum := 0;
  while i < N
    invariant 0 <= i <= N
    invariant sum == i * (i + 1) / 2
  {
    i := i + 1;
    sum := sum + i;
  }
  s := sum;
}
// </vc-code>

