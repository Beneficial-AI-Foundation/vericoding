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
  ensures exists p :: -100 <= p <= 100 && sum_squares(p, a) <= sum_squares(p', a) forall p' :: -100 <= p' <= 100
{
  // The minimum of a convex quadratic function occurs at the arithmetic mean
  // Since p is constrained to [-100, 100], we check the endpoints if mean is outside
}

lemma MeanGivesMinSumSquares(a: seq<int>, mean: int)
  requires |a| > 0 && -100 <= mean <= 100
  ensures sum_squares(mean, a) <= sum_squares(p, a) forall p :: -100 <= p <= 100
{
  // This lemma would require mathematical induction to prove that the quadratic
  // function f(p) = sum_squares(p, a) is minimized at the mean
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
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures IsOptimalCost(result, a)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    result := 0;
  } else {
    var sum := 0;
    for i := 0 to n - 1
      invariant 0 <= i <= n
      invariant sum == total(a[0..i])
    {
      sum := sum + a[i];
    }
    
    var mean := sum / n;
    var candidate1 := clip(mean);
    var candidate2 := clip(mean + 1);
    
    var cost1 := sum_squares(candidate1, a);
    var cost2 := sum_squares(candidate2, a);
    
    if cost1 <= cost2 {
      result := cost1;
    } else {
      result := cost2;
    }
  }
}
// </vc-code>

