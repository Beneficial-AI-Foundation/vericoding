// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SumOfSquaresOfFirstNOddNumbers(n: nat) returns (result: nat)
    requires n >= 0
    ensures result as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    result := 0;
  } else {
    result := (n * (2 * n - 1) * (2 * n + 1)) / 3;
  }
}
// </vc-code>
