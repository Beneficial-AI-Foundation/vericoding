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
lemma MaxSccGroupsCorrect(n: int, m: int)
  requires ValidInput(n, m)
  ensures MaxSccGroups(n, m) >= 0
{
  if n < m / 2 {
    var directGroups := n;
    var remainingCPieces := m - n * 2;
    var additionalGroups := remainingCPieces / 4;
    assert 2*n < m;
    assert remainingCPieces >= 0;
    assert additionalGroups >= 0;
    assert directGroups >= 0;
    assert MaxSccGroups(n, m) == directGroups + additionalGroups;
  } else {
    var directGroups := m / 2;
    var remainingCPieces := m - (m / 2) * 2;
    var additionalGroups := remainingCPieces / 4;
    assert 0 <= remainingCPieces <= 1;
    assert additionalGroups >= 0;
    assert directGroups >= 0;
    assert MaxSccGroups(n, m) == directGroups + additionalGroups;
  }
}

lemma SolveEquivalent(n: int, m: int, result: int)
  requires ValidInput(n, m)
  requires result == MaxSccGroups(n, m)
  ensures result == MaxSccGroups(n, m)
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
  var directGroups := if n < m / 2 then n else m / 2;
  var remainingCPieces := m - directGroups * 2;
  var additionalGroups := remainingCPieces / 4;
  result := directGroups + additionalGroups;
}
// </vc-code>

