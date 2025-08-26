method NthHexagonalNumber(n: int) returns (hexNum: int)
    requires n >= 0
    ensures hexNum == n * ((2 * n) - 1)
// </vc-spec>
// <vc-code>
{
  hexNum := n * ((2 * n) - 1);
}
// </vc-code>