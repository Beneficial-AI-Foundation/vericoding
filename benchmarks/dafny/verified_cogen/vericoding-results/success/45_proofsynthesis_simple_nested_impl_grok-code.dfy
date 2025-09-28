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
  /* code modified by LLM (iteration 2): Introduced count variable to resolve unresolved identifier error */
  sum := N;
  var count := 0;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant sum == N + count
    invariant count <= i
  {
    if b[i] == i + 1 {
      sum := sum + 1;
      count := count + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
