// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SumFormula(n: int): int
  requires n >= 0
{
  n * (n + 1) / 2
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
  if n <= 0 {
    result := (0, 0.0);
  } else {
    var sum := SumFormula(n);
    var avg := sum as real / n as real;
    result := (sum, avg);
  }
}
// </vc-code>
