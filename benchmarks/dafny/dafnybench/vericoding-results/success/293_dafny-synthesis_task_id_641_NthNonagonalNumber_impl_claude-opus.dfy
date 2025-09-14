

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method NthNonagonalNumber(n: int) returns (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
// </vc-spec>
// <vc-code>
{
  number := n * (7 * n - 5) / 2;
}
// </vc-code>

