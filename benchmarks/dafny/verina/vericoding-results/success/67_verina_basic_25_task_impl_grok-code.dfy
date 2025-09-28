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
  /* code modified by LLM (iteration 2): Added handling for negative n to fix invariant verification error */
  if n < 0 {
    result := (0, 0.0);
  } else {
    var sum := 0;
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant sum == i * (i + 1) / 2
    {
      i := i + 1;
      sum := sum + i;
    }
    result := (sum, if n == 0 then 0.0 else sum as real / n as real);
  }
}
// </vc-code>
