predicate ValidInput(n: int, sticks: seq<int>)
{
    1 <= n <= 1000 &&
    |sticks| == n &&
    (forall i :: 0 <= i < |sticks| ==> 1 <= sticks[i] <= 100)
}

function CostForT(sticks: seq<int>, t: int): int
    requires forall i :: 0 <= i < |sticks| ==> 1 <= sticks[i] <= 100
    requires 1 <= t <= 99
    ensures CostForT(sticks, t) >= 0
{
    SumCosts(sticks, t, 0)
}

function SumCosts(sticks: seq<int>, t: int, index: int): int
    requires forall i :: 0 <= i < |sticks| ==> 1 <= sticks[i] <= 100
    requires 1 <= t <= 99
    requires 0 <= index <= |sticks|
    ensures SumCosts(sticks, t, index) >= 0
    decreases |sticks| - index
{
    if index == |sticks| then 0
    else Max(0, Abs(t - sticks[index]) - 1) + SumCosts(sticks, t, index + 1)
}

function Abs(x: int): int
    ensures Abs(x) >= 0
{
    if x >= 0 then x else -x
}

function Max(a: int, b: int): int
    ensures Max(a, b) >= a && Max(a, b) >= b
{
    if a >= b then a else b
}

predicate IsOptimalT(sticks: seq<int>, t: int)
    requires forall i :: 0 <= i < |sticks| ==> 1 <= sticks[i] <= 100
    requires 1 <= t <= 99
{
    forall other_t :: 1 <= other_t <= 99 ==> 
        CostForT(sticks, t) <= CostForT(sticks, other_t)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindOptimalT(n: int, sticks: seq<int>) returns (t: int, min_cost: int)
    requires ValidInput(n, sticks)
    ensures 1 <= t <= 99
    ensures min_cost >= 0
    ensures min_cost == CostForT(sticks, t)
    ensures IsOptimalT(sticks, t)
// </vc-spec>
// <vc-code>
{
  // Establish element bounds for function preconditions
  assert forall i :: 0 <= i < |sticks| ==> 1 <= sticks[i] <= 100;

  var tt := 1;
  var bestT := 1;
  var bestCost := CostForT(sticks, 1);

  while tt < 99
    invariant 1 <= tt <= 99
    invariant 1 <= bestT <= tt
    invariant bestCost == CostForT(sticks, bestT)
    invariant bestCost >= 0
    invariant forall other_t :: 1 <= other_t <= tt ==> bestCost <= CostForT(sticks, other_t)
    decreases 99 - tt
  {
    tt := tt + 1;
    var c := CostForT(sticks, tt);
    if c < bestCost {
      bestT := tt;
      bestCost := c;
    }
  }

  assert tt == 99;
  assert forall other_t :: 1 <= other_t <= 99 ==> bestCost <= CostForT(sticks, other_t);

  t := bestT;
  min_cost := bestCost;
}
// </vc-code>

