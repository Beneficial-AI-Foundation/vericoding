function sum_squares(p: int, a: seq<int>): int
{
    if |a| == 0 then 0
    else (p - a[0]) * (p - a[0]) + sum_squares(p, a[1..])
}

predicate ValidInput(n: int, a: seq<int>)
{
    n >= 1 && n <= 100 && |a| == n && 
    forall i :: 0 <= i < |a| ==> -100 <= a[i] <= 100
}

predicate IsOptimalCost(result: int, a: seq<int>)
{
    result >= 0 &&
    exists p :: -100 <= p <= 100 && result == sum_squares(p, a) &&
    forall p :: -100 <= p <= 100 ==> result <= sum_squares(p, a)
}

// <vc-helpers>
lemma Lemma_SumSquares_NonNeg(p: int, a: seq<int>)
  ensures sum_squares(p, a) >= 0
  decreases |a|
{
  if |a| == 0 {
  } else {
    Lemma_SumSquares_NonNeg(p, a[1..]);
    assert (p - a[0]) * (p - a[0]) >= 0;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures IsOptimalCost(result, a)
// </vc-spec>
// <vc-code>
{
  var bestP := -100;
  var bestCost := sum_squares(bestP, a);
  Lemma_SumSquares_NonNeg(bestP, a);
  var i := -99;
  while i <= 100
    invariant -99 <= i <= 101
    invariant -100 <= bestP <= i - 1
    invariant bestCost == sum_squares(bestP, a)
    invariant forall p :: -100 <= p <= i - 1 ==> bestCost <= sum_squares(p, a)
    invariant bestCost >= 0
    decreases 101 - i
  {
    var c := sum_squares(i, a);
    Lemma_SumSquares_NonNeg(i, a);
    if c < bestCost {
      bestCost := c;
      bestP := i;
    }
    i := i + 1;
  }
  assert i == 101;
  result := bestCost;
  assert result >= 0;
  assert -100 <= bestP <= 100;
  assert result == sum_squares(bestP, a);
  assert -100 <= bestP <= 100 && result == sum_squares(bestP, a);
  assert exists p: int :: -100 <= p <= 100 && result == sum_squares(p, a);
  assert forall p :: -100 <= p <= 100 ==> result <= sum_squares(p, a);
}
// </vc-code>

