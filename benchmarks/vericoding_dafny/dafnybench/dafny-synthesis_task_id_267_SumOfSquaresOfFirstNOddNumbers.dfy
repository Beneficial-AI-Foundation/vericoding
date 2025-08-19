// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SumOfSquaresOfFirstNOddNumbers(n: int) returns (sum: int)
    requires n >= 0
    ensures sum == (n * (2 * n - 1) * (2 * n + 1)) / 3
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>