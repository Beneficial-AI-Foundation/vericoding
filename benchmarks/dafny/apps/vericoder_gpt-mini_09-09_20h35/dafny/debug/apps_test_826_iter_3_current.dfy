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
lemma TriangularGreater(n: int)
  requires n >= 1
  ensures (2 + n) * (n + 1) / 2 > n + 1
{
  // (n+2) > 2 for n >= 1, and (n+1) > 0, so product > 2*(n+1)
  assert 2 + n > 2;
  assert n + 1 > 0;
  assert (2 + n) * (n + 1) > 2 * (n + 1);
  // divide both sides by 2 (>0)
  assert (2 + n) * (n + 1) / 2 > n + 1;
}

lemma BaseLeq(n:int)
  requires n >= 1
  ensures (2 + 0) * (0 + 1) / 2 <= n + 1
{
  // (2+0)*(0+1)/2 = 1 <= n+1 for n>=1
  assert 1 <= n + 1;
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
  var s := 0;
  while !((2 + s) * (s + 1) / 2 > n + 1)
    invariant 0 <= s <= n
    invariant forall j :: { (2 + j) * (j + 1) / 2 } 0 <= j && j < s ==> (2 + j) * (j + 1) / 2 <= n + 1
    decreases n - s + 1
  {
    s := s + 1;
  }

  // At loop exit we have (2+s)*(s+1)/2 > n+1
  assert (2 + s) * (s + 1) / 2 > n + 1;

  // s cannot be 0: if s==0 then 1 > n+1 which contradicts n >= 1
  if s == 0 {
    assert 1 > n + 1;
    assert 1 <= n + 1;
    assert false;
  }

  result := n - s + 1;

  // result bounds: since s >= 1 and s <= n, 1 <= result <= n
  assert result >= 1;
  assert result <= n;

  // Prove existence of minimal savings witness
  // IsOptimalSavings: s >= 0, (2+s)*(s+1)/2 > n+1, and previous <= n+1 (for s>0)
  assert s >= 0;
  assert (2 + s) * (s + 1) / 2 > n + 1;
  if s > 0 {
    // Use the invariant to instantiate for j := s-1
    assert 0 <= s - 1;
    assert s - 1 < s;
    assert forall j :: { (2 + j) * (j + 1) / 2 } 0 <= j && j < s ==> (2 + j) * (j + 1) / 2 <= n + 1;
    assert (2 + (s - 1)) * ((s - 1) + 1) / 2 <= n + 1;
  }
  assert IsOptimalSavings(n, s);
  // The invariant gives the forall needed for IsMinimalSavings
  assert forall j :: { (2 + j) * (j + 1) / 2 } j >= 0 && j < s ==> (2 + j) * (j + 1) / 2 <= n + 1;
  assert IsMinimalSavings(n, s);

  // result matches OptimalCost for this savings
  assert result == OptimalCost(n, s);

  assert exists savings :: IsMinimalSavings(n, savings) && result == OptimalCost(n, savings);
}
// </vc-code>

