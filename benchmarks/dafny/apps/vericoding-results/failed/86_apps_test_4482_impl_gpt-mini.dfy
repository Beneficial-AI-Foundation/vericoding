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
lemma SumSquaresNonnegative(p: int, a: seq<int>)
  ensures sum_squares(p, a) >= 0
  decreases |a|
{
  if |a| == 0 {
    // sum_squares(p, []) == 0
  } else {
    assert (p - a[0]) * (p - a[0]) >= 0;
    SumSquaresNonnegative(p, a[1..]);
    assert sum_squares(p, a) == (p - a[0]) * (p - a[0]) + sum_squares(p, a[1..]);
    assert sum_squares(p, a) >= 0;
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
  var p := -100;
  var bestp := p;
  var best := sum_squares(p, a);
  p := p + 1;
  while p <= 100
    invariant -100 <= p <= 101
    invariant -100 <= bestp <= 100
    invariant best == sum_squares(bestp, a)
    invariant forall q :: -100 <= q < p ==> best <= sum_squares(q, a)
  {
    var s := sum_squares(p, a);
    if s < best {
      best := s;
      bestp := p;
    }
    // after possibly updating best to s, we know best <= s
    assert best <= s;
    p := p + 1;
  }
  // From the loop invariant and the negation of the guard we get p == 101
  assert p == 101;
  // Use invariants to establish the postconditions
  assert -100 <= bestp <= 100;
  assert best == sum_squares(bestp, a);
  assert forall q :: -100 <= q <= 100 ==> best <= sum_squares(q, a);
  assert (exists q :: q == bestp && -100 <= q <= 100 && best == sum_squares(q, a));
  SumSquaresNonnegative(bestp, a);
  result := best;
}
// </vc-code>

