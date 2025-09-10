predicate ValidInput(n: int)
{
  n >= 1
}

predicate IsOptimalSavings(n: int, savings: int)
  requires n >= 1
{
  savings >= 0 &&
  (2 + savings) * (savings + 1) / 2 > n + 1 &&
  (savings == 0 || (2 + (savings - 1)) * savings / 2 <= n + 1)
}

predicate IsMinimalSavings(n: int, savings: int)
  requires n >= 1
{
  IsOptimalSavings(n, savings) &&
  (forall j :: j >= 0 && j < savings ==> (2 + j) * (j + 1) / 2 <= n + 1)
}

function OptimalCost(n: int, savings: int): int
  requires n >= 1
  requires IsOptimalSavings(n, savings)
{
  n - savings + 1
}

// <vc-helpers>
function findMinimalSavings(n: int): int
  requires n >= 1
  ensures var s := findMinimalSavings(n); IsMinimalSavings(n, s)
  decreases n
{
  var s := 0;
  while (2 + s) * (s + 1) / 2 <= n + 1
    invariant s >= 0
    invariant (s == 0 || (2 + (s - 1)) * s / 2 <= n + 1)
    invariant forall j :: j >= 0 && j < s ==> (2 + j) * (j + 1) / 2 <= n + 1
    decreases n + 1 - (2 + s) * (s + 1) / 2
  {
    s := s + 1;
  }
  return s - 1; // The loop overshoots by 1, so subtract 1.
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
  requires ValidInput(n)
  ensures result >= 1
  ensures result <= n
  ensures exists savings :: IsMinimalSavings(n, savings) && result == OptimalCost(n, savings)
// </vc-spec>
// <vc-code>
{
  var savings := 0;
  while (2 + savings) * (savings + 1) / 2 <= n + 1
    invariant savings >= 0
    invariant forall j :: 0 <= j < savings ==> (2 + j) * (j + 1) / 2 <= n + 1
    decreases n + 1 - (2 + savings) * (savings + 1) / 2
  {
    savings := savings + 1;
  }
  savings := savings - 1; // The loop overshoots by 1, so subtract 1.
  result := n - savings + 1;
}
// </vc-code>

