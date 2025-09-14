predicate ValidInput(n: int, m: int)
{
    n >= 0 && m >= 0
}

function MaxSccGroups(n: int, m: int): int
  requires ValidInput(n, m)
{
    var directGroups := if n < m / 2 then n else m / 2;
    var remainingCPieces := m - directGroups * 2;
    var additionalGroups := remainingCPieces / 4;
    directGroups + additionalGroups
}

// <vc-helpers>
lemma DivByPosNonNeg(x: int, d: int)
  requires x >= 0
  requires d > 0
  ensures x / d >= 0
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
  requires ValidInput(n, m)
  ensures result >= 0
  ensures result == MaxSccGroups(n, m)
// </vc-spec>
// <vc-code>
{
  var half := m / 2;
  var directGroups := if n < half then n else half;
  var remainingCPieces := m - directGroups * 2;

  assert directGroups <= half;
  assert 2 * directGroups <= 2 * half;
  assert m - 2 * half >= 0;
  assert remainingCPieces >= m - 2 * half;

  var additionalGroups := remainingCPieces / 4;
  DivByPosNonNeg(remainingCPieces, 4);
  assert additionalGroups >= 0;
  assert directGroups >= 0;
  assert remainingCPieces >= 0;

  result := directGroups + additionalGroups;

  assert result >= 0;
  assert result == MaxSccGroups(n, m);
}
// </vc-code>

