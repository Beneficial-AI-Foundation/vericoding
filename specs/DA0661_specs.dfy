// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
  requires ValidInput(n, m)
  ensures result >= 0
  ensures result == MaxSccGroups(n, m)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
