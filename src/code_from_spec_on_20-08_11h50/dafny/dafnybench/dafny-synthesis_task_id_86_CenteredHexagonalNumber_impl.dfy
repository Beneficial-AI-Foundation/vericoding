method CenteredHexagonalNumber(n: nat) returns (result: nat)
    requires n >= 0
    ensures result == 3 * n * (n - 1) + 1
// </vc-spec>
// <vc-code>
{
  result := 3 * n * (n - 1) + 1;
}
// </vc-code>