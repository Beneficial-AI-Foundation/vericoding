predicate ValidInput(n: int, m: int)
{
  n >= 1 && m >= 1
}

function OptimalVasyaScore(n: int, m: int): int
  requires ValidInput(n, m)
{
  if n < m then n else m
}

function OptimalPetyaScore(n: int, m: int): int
  requires ValidInput(n, m)
{
  n + m - 1 - OptimalVasyaScore(n, m)
}

function TotalAdjacentPairs(n: int, m: int): int
  requires ValidInput(n, m)
{
  n + m - 1
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (petyaScore: int, vasyaScore: int)
  requires ValidInput(n, m)
  ensures vasyaScore == OptimalVasyaScore(n, m)
  ensures petyaScore == OptimalPetyaScore(n, m)
  ensures petyaScore + vasyaScore == TotalAdjacentPairs(n, m)
// </vc-spec>
// <vc-code>
{
  if n < m {
    vasyaScore := n;
  } else {
    vasyaScore := m;
  }
  petyaScore := n + m - 1 - vasyaScore;
}
// </vc-code>

