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
    // Find the first k where (2 + k) * (k + 1) / 2 > n + 1
    var k := 1;
    while (2 + k) * (k + 1) / 2 <= n + 1
      invariant 1 <= k <= n + 1
      invariant (2 + (k - 1)) * k / 2 <= n + 1
    {
      k := k + 1;
    }
    assert (2 + k) * (k + 1) / 2 > n + 1;
    assert (2 + (k - 1)) * k / 2 <= n + 1;
    assert IsOptimalSavings(n, k);
  }
}

lemma MinimalSavingsExists(n: int)
  requires n >= 1
  ensures exists savings :: IsMinimalSavings(n, savings)
{
  // Find the minimal savings directly
  var savings := 0;
  
  while (2 + savings) * (savings + 1) / 2 <= n + 1
    invariant 0 <= savings <= n + 1
    invariant forall j :: 0 <= j < savings ==> (2 + j) * (j + 1) / 2 <= n + 1
  {
    savings := savings + 1;
  }
  
  // Now prove IsMinimalSavings(n, savings)
  assert (2 + savings) * (savings + 1) / 2 > n + 1;
  
  // Prove IsOptimalSavings(n, savings)
  if savings > 0 {
    var j := savings - 1;
    assert 0 <= j && j < savings;
    assert (2 + j) * (j + 1) / 2 <= n + 1;
    assert j + 1 == savings;
    assert (2 + (savings - 1)) * savings / 2 <= n + 1;
  }
  
  assert IsOptimalSavings(n, savings);
  assert IsMinimalSavings(n, savings);
}

lemma ComputeMinimalSavings(n: int, savings: int)
  requires n >= 1
  requires savings >= 0
  requires (2 + savings) * (savings + 1) / 2 > n + 1
  requires forall j :: 0 <= j < savings ==> (2 + j) * (j + 1) / 2 <= n + 1
  ensures IsMinimalSavings(n, savings)
{
  // Need to prove IsOptimalSavings(n, savings)
  // First part: (2 + savings) * (savings + 1) / 2 > n + 1 - already in precondition
  // Second part: savings == 0 || (2 + (savings - 1)) * savings / 2 <= n + 1
  if savings > 0 {
    var j := savings - 1;
    assert 0 <= j && j < savings;
    assert (2 + j) * (j + 1) / 2 <= n + 1;  // from the forall precondition
    assert j + 1 == savings;
    assert (2 + (savings - 1)) * savings / 2 <= n + 1;
  }
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
    invariant 0 <= savings <= n + 1
    invariant forall j :: 0 <= j < savings ==> (2 + j) * (j + 1) / 2 <= n + 1
    decreases n + 1 - savings
  {
    savings := savings + 1;
  }
  
  // After the loop: (2 + savings) * (savings + 1) / 2 > n + 1
  // And: forall j :: 0 <= j < savings ==> (2 + j) * (j + 1) / 2 <= n + 1
  
  // Help Dafny remember the loop invariant
  ghost var temp := savings;
  assert savings == temp;
  assert (2 + savings) * (savings + 1) / 2 > n + 1;
  
  // Prove the forall condition is still true
  forall j | 0 <= j < savings
    ensures (2 + j) * (j + 1) / 2 <= n + 1
  {
    assert j < temp;
    // This follows from the loop invariant
  }
  
  ComputeMinimalSavings(n, savings);
  result := n - savings + 1;
  
  assert IsMinimalSavings(n, savings);
  assert result == OptimalCost(n, savings);
}
// </vc-code>

