// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function RHS(n: nat): int { (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3 }
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
    var nn := n as int;
    result := ((nn * (2 * nn - 1) * (2 * nn + 1)) / 3) as nat;
  }
}
// </vc-code>
