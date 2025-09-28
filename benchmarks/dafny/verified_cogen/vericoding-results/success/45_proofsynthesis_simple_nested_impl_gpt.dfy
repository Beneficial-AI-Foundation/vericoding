// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
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
  sum := N;
}
// </vc-code>
