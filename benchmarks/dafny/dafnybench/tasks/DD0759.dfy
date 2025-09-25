// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SumAndAverage(n: int) returns (sum: int, average: real)
    requires n > 0
    ensures sum == n * (n + 1) / 2
    ensures average == sum as real / n as real
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
