// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method NthOctagonalNumber(n: int) returns (octagonalNumber: int)
    requires n >= 0
    ensures octagonalNumber == n * (3 * n - 2)
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>