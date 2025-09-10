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
function CalculateDirectGroups(n: int, m: int): int
  requires ValidInput(n, m)
  ensures 0 <= CalculateDirectGroups(n, m) <= n
  ensures CalculateDirectGroups(n, m) <= m / 2
{
    if n < m / 2 then n else m / 2
}

function CalculateRemainingCPieces(n: int, m: int): int
  requires ValidInput(n, m)
  ensures CalculateRemainingCPieces(n, m) >= 0
{
  var directGroups := CalculateDirectGroups(n, m);
  (m - directGroups * 2)
}

function CalculateAdditionalGroups(n: int, m: int): int
  requires ValidInput(n, m)
  ensures CalculateAdditionalGroups(n, m) >= 0
{
  var remainingCPieces := CalculateRemainingCPieces(n, m);
  (remainingCPieces / 4)
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
  var directGroups: int;
  if n < m / 2
  {
    directGroups := n;
  }
  else
  {
    directGroups := m / 2;
  }

  var remainingCPieces := m - directGroups * 2;
  var additionalGroups := remainingCPieces / 4;
  result := directGroups + additionalGroups;
}
// </vc-code>

