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
lemma SumFormula(k: int)
  requires k >= 0
  ensures (2 + k) * (k + 1) / 2 == (k + 1) * (k + 2) / 2
{
}

lemma SumIncreasing(k1: int, k2: int)
  requires k1 >= 0 && k2 >= k1
  ensures (2 + k1) * (k1 + 1) / 2 <= (2 + k2) * (k2 + 1) / 2
{
}

lemma OptimalSavingsExists(n: int) returns (savings: int)
  requires n >= 1
  ensures IsOptimalSavings(n, savings)
{
  savings := 0;
  while (2 + savings) * (savings + 1) / 2 <= n + 1
    invariant savings >= 0
    invariant (2 + savings) * (savings + 1) / 2 <= n + 1 ==> savings < n + 2
  {
    savings := savings + 1;
  }
}

lemma MinimalSavingsUnique(n: int, s1: int, s2: int)
  requires n >= 1
  requires IsMinimalSavings(n, s1)
  requires IsMinimalSavings(n, s2)
  ensures s1 == s2
{
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
    invariant savings == 0 || (2 + (savings - 1)) * savings / 2 <= n + 1
  {
    savings := savings + 1;
  }
  
  result := n - savings + 1;
}
// </vc-code>

