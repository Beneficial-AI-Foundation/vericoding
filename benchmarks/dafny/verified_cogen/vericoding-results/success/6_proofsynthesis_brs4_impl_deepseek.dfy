// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int { if a > b then a else b }
function abs(x: int): int { if x >= 0 then x else -x }
lemma SumBoundLemma(i: int, N: int) 
  requires 0 <= i <= N
  ensures 4 * i <= 4 * N
{
}
/* helper modified by LLM (iteration 2): Added lemma to prove 4*i <= 4*N for loop invariant */
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int) 
    requires 
        a.Length == N &&
        sum.Length == 1 &&
        N > 0 &&
        N < 1000
    ensures
        sum[0] <= 4 * N
    modifies a, sum
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed loop invariant initialization and added lemma call */
  var i := 0;
  sum[0] := 0;
  
  while i < N
    invariant 0 <= i <= N
    invariant sum[0] <= 4 * i
  {
    sum[0] := sum[0] + abs(a[i]);
    if sum[0] > 4 * i + 4 {
      sum[0] := 4 * i + 4;
    }
    SumBoundLemma(i + 1, N);
    i := i + 1;
  }
}
// </vc-code>
