// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  var sum := if n <= 0 then 0 else (n * (n + 1)) / 2;
  var average := if n == 0 then 0.0 else (sum as real) / (n as real);
  result := (sum, average);
}
// </vc-code>
