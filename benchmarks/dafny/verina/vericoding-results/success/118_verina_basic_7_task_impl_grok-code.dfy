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
  var i: nat := 0;
  var sum: nat := 0;
  var odd: nat := 1;
  while i < n
    invariant i <= n
    invariant sum as int == (i as int * (2 * i as int - 1) * (2 * i as int + 1)) / 3
    invariant odd == 2 * i + 1
  {
    sum := sum + odd * odd;
    odd := odd + 2;
    i := i + 1;
  }
  result := sum;
}
// </vc-code>
