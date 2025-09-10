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
lemma OptimalSavingsExists(n: int)
  requires n >= 1
  ensures exists savings :: IsOptimalSavings(n, savings)
{
  if (2 + 0) * (0 + 1) / 2 > n + 1 {
    assert IsOptimalSavings(n, 0);
  } else {
    var k := n;
    assert (2 + k) * (k + 1) / 2 >= (k + 1) * (k + 1) / 2 >= n + 1;
    assert IsOptimalSavings(n, k);
  }
}

lemma MinimalSavingsExists(n: int)
  requires n >= 1
  ensures exists savings :: IsMinimalSavings(n, savings)
{
  OptimalSavingsExists(n);
  var witnesses := set s | 0 <= s <= n && IsOptimalSavings(n, s);
  assert witnesses != {};
  
  var minSavings :| minSavings in witnesses && forall s :: s in witnesses ==> minSavings <= s;
  
  forall j | j >= 0 && j < minSavings
    ensures (2 + j) * (j + 1) / 2 <= n + 1
  {
    if (2 + j) * (j + 1) / 2 > n + 1 {
      assert IsOptimalSavings(n, j);
      assert j in witnesses;
      assert false;
    }
  }
  
  assert IsMinimalSavings(n, minSavings);
}

lemma ComputeMinimalSavings(n: int, savings: int)
  requires n >= 1
  requires savings >= 0
  requires (2 + savings) * (savings + 1) / 2 > n + 1
  requires forall j :: 0 <= j < savings ==> (2 + j) * (j + 1) / 2 <= n + 1
  ensures IsMinimalSavings(n, savings)
{
  assert IsOptimalSavings(n, savings);
  assert IsMinimalSavings(n, savings);
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
    invariant 0 <= savings <= n
    invariant forall j :: 0 <= j < savings ==> (2 + j) * (j + 1) / 2 <= n + 1
  {
    savings := savings + 1;
  }
  
  ComputeMinimalSavings(n, savings);
  result := n - savings + 1;
  
  assert IsMinimalSavings(n, savings);
  assert result == OptimalCost(n, savings);
}
// </vc-code>

