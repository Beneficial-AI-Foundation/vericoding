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
// No additional helper code required.
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
  var best_t := 1;
  var best_cost := CostForT(sticks, 1);
  var tcur := 2;
  while tcur <= 99
    invariant 1 <= best_t <= 99
    invariant 1 <= tcur <= 100
    invariant best_cost == CostForT(sticks, best_t)
    invariant forall tt :: 1 <= tt < tcur ==> CostForT(sticks, tt) >= best_cost
    decreases 100 - tcur
  {
    var idx := |sticks|;
    var cost := 0;
    while idx > 0
      invariant 0 <= idx <= |sticks|
      invariant cost == SumCosts(sticks, tcur, idx)
      decreases idx
    {
      idx := idx - 1;
      cost := cost + Max(0, Abs(tcur - sticks[idx]) - 1);
    }
    // now cost == CostForT(sticks, tcur)
    if cost < best_cost {
      best_cost := cost;
      best_t := tcur;
    }
    tcur := tcur + 1;
  }
  t := best_t;
  min_cost := best_cost;
}
// </vc-code>

