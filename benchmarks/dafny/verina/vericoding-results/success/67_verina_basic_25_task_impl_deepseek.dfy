// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
method ComputeSum(n: int) returns (s: int)
  requires n <= 100000 && n >= 0
  ensures s == (n * (n + 1)) / 2
  decreases n
{
  if n == 0 {
    s := 0;
  } else {
    var prev := ComputeSum(n - 1);
    s := prev + n;
  }
}

function IntToReal(n: int): real
  ensures IntToReal(n) == n as real
{
  n as real
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
  /* code modified by LLM (iteration 3): add precondition check and handle negative n */
  result := (0, 0.0);
  if n <= 0 {
    result := (0, 0.0);
  } else {
    var sum := ComputeSum(n);
    var avg := (sum as real) / (n as real);
    result := (sum, avg);
  }
}
// </vc-code>
