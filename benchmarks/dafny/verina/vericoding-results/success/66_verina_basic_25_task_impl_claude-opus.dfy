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
  if n == 0 {
    result := (0, 0.0);
  } else if n > 0 {
    var sum := n * (n + 1) / 2;
    result := (sum, 0.0);
  } else {
    var sum := (-n) * ((-n) + 1) / 2;
    result := (-sum, 0.0);
  }
}
// </vc-code>
