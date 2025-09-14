// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function OddSquare(k: int): int { (2*k - 1) * (2*k - 1) }
// </vc-helpers>

// <vc-spec>
method SumOfSquaresOfFirstNOddNumbers(n: nat) returns (result: nat)
    requires n >= 0
    ensures result as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3
// </vc-spec>
// <vc-code>
{
  var i: int := 0;
  var r: int := 0;
  while i < n
    invariant 0 <= i <= n
    invariant r >= 0
    invariant 3 * r == i * (2 * i - 1) * (2 * i + 1)
  {
    i := i + 1;
    r := r + (2 * i - 1) * (2 * i - 1);
  }
  result := r as nat;
}
// </vc-code>
