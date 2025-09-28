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
/* code modified by LLM (iteration 4): Added guard for loop to avoid compilation error when N<=0 */
{
  var count := 0;
  if N > 0 {
    for i := 0 to N-1
      invariant 0 <= count <= i
    {
      count := count + (if b[i] != i then 1 else 0);
    }
  }
  sum := N + count;
}
// </vc-code>
