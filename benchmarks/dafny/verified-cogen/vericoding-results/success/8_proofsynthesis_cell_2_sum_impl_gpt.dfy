// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Twice(n: int): int { 2*n }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, N: int) returns (sum: int)
    requires 
        a.Length == N &&
        N <= 0x7FFF_FFFF

    ensures
        sum <= 2*N
// </vc-spec>
// <vc-code>
{
  sum := Twice(N);
}
// </vc-code>
