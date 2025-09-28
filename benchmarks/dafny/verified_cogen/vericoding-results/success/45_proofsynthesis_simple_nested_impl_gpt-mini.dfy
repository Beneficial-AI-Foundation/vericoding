// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): express difference bounds without using 'result' */
function Diff(k: int, bk: int): int
  requires k <= bk && bk <= k + 1
  ensures 0 <= bk - k && bk - k <= 1
{ bk - k }
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
  /* code modified by LLM (iteration 3): accumulate sum using Diff and maintain invariants */
  sum := 0;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant i <= sum <= 2*i
  {
    var v := Diff(i, b[i]);
    sum := sum + 1 + v;
    i := i + 1;
  }
}
// </vc-code>
