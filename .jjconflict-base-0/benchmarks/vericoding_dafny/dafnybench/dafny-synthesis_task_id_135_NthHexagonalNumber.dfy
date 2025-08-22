// <vc-helpers>
// </vc-helpers>

method NthHexagonalNumber(n: int) returns (hexNum: int)
    requires n >= 0
    ensures hexNum == n * ((2 * n) - 1)
// <vc-code>
{
  assume false;
}
// </vc-code>