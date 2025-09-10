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
lemma MinSumSquaresLemma(a: seq<int>)
  requires |a| > 0
  ensures exists p :: -100 <= p <= 100 && (forall p' :: -100 <= p' <= 100 ==> sum_squares(p, a) <= sum_squares(p', a))
{
}

lemma MeanGivesMinSumSquares(a: seq<int>, mean: int)
  requires |a| > 0 && -100 <= mean <= 100
  ensures forall p :: -100 <= p <= 100 ==> sum_squares(mean, a) <= sum_squares(p, a)
{
}

function total(a: seq<int>): int
  requires |a| >= 0
{
  if |a| == 0 then 0 else a[0] + total(a[1..])
}

lemma MeanProperty(a: seq<int>)
  requires |a| > 0
  ensures (total(a) / |a|) in [-100, 100] || total(a) / |a| < -100 || total(a) / |a| > 100
{
}

function clip(p: int): int
{
  if p < -100 then -100
  else if p > 100 then 100
  else p
}

lemma ClipBounds(p: int)
  ensures -100 <= clip(p) <= 100
{
}

lemma SumSquaresConvex(a: seq<int>, p1: int, p2: int, t: real)
  requires 0.0 <= t <= 1.0
  ensures sum_squares(p1, a) <= (1.0 - t) * sum_squares(p1, a) + t * sum_squares(p2, a) as int
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures IsOptimalCost(result, a)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var min_cost := 1000000000;
  var p := -100;
  while p <= 100
    invariant -101 <= p <= 101
    invariant min_cost >= 0
    invariant exists q :: -100 <= q <= p-1 && min_cost == sum_squares(q, a) && (forall r :: -100 <= r <= p-1 ==> min_cost <= sum_squares(r, a))
    decreases 101 - p
  {
    var cost := sum_squares(p, a);
    if cost < min_cost {
      min_cost := cost;
    }
    p := p + 1;
  }
  result := min_cost;
}
// </vc-code>

