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
  assert 2 + n > 2;
  assert n + 1 > 0;
  assert (2 + n) * (n + 1) > 2 * (n + 1);
  assert (2 + n) * (n + 1) / 2 > n + 1;
}

lemma BaseLeq(n:int)
  requires n >= 1
  ensures (2 + 0) * (0 + 1) / 2 <= n + 1
{
  assert 1 <= n + 1;
}

lemma PrevFromInvariant(n:int, s:int)
  requires n >= 1
  requires s > 0
  requires forall j :: {:trigger ((2 + j) * (j + 1) / 2)} 0 <= j && j < s ==> (2 + j) * (j + 1) / 2 <= n + 1
  ensures (2 + (s - 1)) * ((s - 1) + 1) / 2 <= n + 1
{
  var j := s - 1;
  assert 0 <= j && j < s;
  assert (2 + j) * (j + 1) / 2 <= n + 1;
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
    invariant forall j :: {:trigger ((2 + j) * (j + 1) / 2)} 0 <= j && j < s ==> (2 + j) * (j + 1) / 2 <= n + 1
    decreases n - s + 1
  {
    if s == n {
      TriangularGreater(n);
      assert (2 + s) * (s + 1) / 2 > n + 1;
      assert (2 + s) * (s + 1) / 2 <= n + 1;
      assert false;
    }
    s := s + 1;
  }

  assert (2 + s) * (s + 1) / 2 > n + 1;

  if s == 0 {
    assert 1 > n + 1;
    assert 1 <= n + 1;
    assert false;
  }

  result := n - s + 1;

  assert result >= 1;
  assert result <= n;

  assert s >= 0;
  assert (2 + s) * (s + 1) / 2 > n + 1;

  if s == 0 {
    // this branch is unreachable, but provide the needed fact for the prover
    BaseLeq(n);
  } else {
    PrevFromInvariant(n, s);
  }

  assert IsOptimalSavings(n, s);
  assert forall j :: {:trigger ((2 + j) * (j + 1) / 2)} j >= 0 && j < s ==> (2 + j) * (j + 1) / 2 <= n + 1;
  assert IsMinimalSavings(n, s);

  assert result == OptimalCost(n, s);

  assert exists savings :: IsMinimalSavings(n, savings) && result == OptimalCost(n, savings);
}
// </vc-code>

