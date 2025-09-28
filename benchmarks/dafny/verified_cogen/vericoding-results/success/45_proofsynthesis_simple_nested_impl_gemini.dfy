// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SimpleNested(a: array<int>, b: array<int>, N: int) returns (sum: int)
    requires forall k :: 0 <= k < b.Length ==> k <= b[k] <= k + 1
    requires a.Length == N
    requires b.Length == N
    requires N <= 0x3FFF_FFFF
    ensures N <= sum <= 2*N
// </vc-spec>
// <vc-code>
{
  sum := 0;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant i <= sum <= 2 * i
  {
    sum := sum + (b[i] - i + 1);
    i := i + 1;
  }
}
// </vc-code>
