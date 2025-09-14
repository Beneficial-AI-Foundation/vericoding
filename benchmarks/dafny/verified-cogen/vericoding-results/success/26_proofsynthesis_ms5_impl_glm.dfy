// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int) 
    requires 
        a.Length == N &&
        sum.Length == 1 &&
        N > 0 &&
        N < 1000
    modifies sum
    ensures
        sum[0] <= 4 * N
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added loop invariant to prove postcondition */
  var total := 0;
  for i := 0 to N
    invariant total <= 4 * i
  {
    total := total + min(a[i], 4);
  }
  sum[0] := total;
}
// </vc-code>
