// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SumToN(n: int): int
  requires 0 <= n && n < 100000
  ensures n == 0 ==> SumToN(n) == 0
  ensures n > 0 ==> SumToN(n) == (n * (n + 1)) / 2
{
  if n == 0 then 0 else n + SumToN(n-1)
}
// </vc-helpers>

// <vc-spec>
method SumAndAverage(n: int) returns (result: (int, real))
    requires n < 100000  // reasonable bound to prevent overflow
    ensures
        n == 0 ==> result.0 == 0
    ensures
        n > 0 ==> result.0 == (n * (n + 1)) / 2
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed result reference in ensures clauses */
  if n <= 0 {
    result := (0, 0.0);
  } else {
    var sum := SumToN(n);
    var avg: real := sum as real / n as real;
    result := (sum, avg);
  }
}
// </vc-code>
