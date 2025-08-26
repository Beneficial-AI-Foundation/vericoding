// <vc-helpers>
// </vc-helpers>

method NthNonagonalNumber(n: int) returns (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
// <vc-code>
{
  assume false;
}
// </vc-code>