// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Zero(): int { 0 }

lemma ZeroLe2N(N: int)
  requires N > 0
  ensures Zero() <= 2 * N
{
}

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int) 
    requires 
        a.Length == N &&
        sum.Length == 1 &&
        N > 0 &&
        N < 1000
    ensures
        sum[0] <= 2 * N
    modifies a, sum
// </vc-spec>
// <vc-code>
{
  sum[0] := 0;
}

// </vc-code>
