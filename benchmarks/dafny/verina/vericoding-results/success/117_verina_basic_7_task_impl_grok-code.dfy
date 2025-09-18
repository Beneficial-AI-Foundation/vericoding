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
  var temp1 := 2 * n;
  var temp2 := temp1 - 1;
  var temp3 := temp1 + 1;
  result := n * temp2 * temp3 / 3;
}
// </vc-code>
