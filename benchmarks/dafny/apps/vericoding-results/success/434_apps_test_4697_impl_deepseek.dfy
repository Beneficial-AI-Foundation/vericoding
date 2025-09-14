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
lemma MaxSccGroupsLemma(n: int, m: int, directGroups: int, remainingCPieces: int, additionalGroups: int)
  requires ValidInput(n, m)
  requires directGroups == (if n < m / 2 then n else m / 2)
  requires remainingCPieces == m - directGroups * 2
  requires additionalGroups == remainingCPieces / 4
  ensures directGroups + additionalGroups == MaxSccGroups(n, m)
{
}

lemma DivisionLemma(x: int, d: int)
  requires d > 0
  ensures x / d * d <= x < (x / d + 1) * d
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
  if n < m / 2 {
    result := n;
    var rem := m - 2 * n;
    result := result + rem / 4;
  } else {
    result := m / 2;
    var rem := m - 2 * result;
    result := result + rem / 4;
  }
}
// </vc-code>

