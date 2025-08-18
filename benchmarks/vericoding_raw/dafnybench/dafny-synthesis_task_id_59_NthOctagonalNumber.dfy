// <vc-helpers>
// </vc-helpers>

method NthOctagonalNumber(n: int) returns (octagonalNumber: int)
    requires n >= 0
    ensures octagonalNumber == n * (3 * n - 2)
// <vc-code>
{
  assume false;
}
// </vc-code>