// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function zero(): int { 0 }
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
        sum[0] <= 2 * N
// </vc-spec>
// <vc-code>
{
  sum[0] := 0;
}
// </vc-code>
