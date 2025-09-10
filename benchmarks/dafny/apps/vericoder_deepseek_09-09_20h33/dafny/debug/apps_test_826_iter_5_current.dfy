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
lemma {:induction false} ArithmeticSum(s: int) 
  requires s >= 0
  ensures (2 + s) * (s + 1) / 2 == (s * s + 3*s + 2) / 2
{
}

lemma FindSavings(n: int) returns (s: int)
  requires n >= 1
  ensures IsMinimalSavings(n, s)
{
  var s0 := 0;
  while (2 + s0) * (s0 + 1) / 2 <= n + 1
    invariant s0 >= 0
    invariant (2 + (s0 - 1)) * s0 / 2 <= n + 1 || s0 == 0
    invariant forall j {:trigger (2 + j) * (j + 1) / 2} :: 0 <= j < s0 ==> (2 + j) * (j + 1) / 2 <= n + 1
  {
    s0 := s0 + 1;
  }
  s := s0 - 1;
  assert (2 + s) * (s + 1) / 2 <= n + 1;
  assert (2 + (s + 1)) * (s + 2) / 2 > n + 1;
  assert forall j {:trigger (2 + j) * (j + 1) / 2} :: j >= 0 && j < s ==> (2 + j) * (j + 1) / 2 <= n + 1;
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
    invariant (2 + (savings - 1)) * savings / 2 <= n + 1 || savings == 0
    invariant forall j {:trigger (2 + j) * (j + 1) / 2} :: 0 <= j < savings ==> (2 + j) * (j + 1) / 2 <= n + 1
  {
    savings := savings + 1;
  }
  savings := savings - 1;
  assert IsMinimalSavings(n, savings);
  result := n - savings + 1;
  assert exists savings' :: IsMinimalSavings(n, savings') && result == OptimalCost(n, savings') by {
    var savings' := savings;
  }
}
// </vc-code>

