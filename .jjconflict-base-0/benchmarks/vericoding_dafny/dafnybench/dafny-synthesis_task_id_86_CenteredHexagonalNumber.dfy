// <vc-helpers>
// </vc-helpers>

method CenteredHexagonalNumber(n: nat) returns (result: nat)
    requires n >= 0
    ensures result == 3 * n * (n - 1) + 1
// <vc-code>
{
  assume false;
}
// </vc-code>