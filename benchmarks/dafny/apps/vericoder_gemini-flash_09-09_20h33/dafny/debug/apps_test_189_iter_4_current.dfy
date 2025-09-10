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
function CheapestCost(sticks: seq<int>): int
    requires forall i :: 0 <= i < |sticks| ==> 1 <= sticks[i] <= 100
    ensures CheapestCost(sticks) >= 0
{
    if |sticks| == 0 then 0
    else
        var min_cost := CostForT(sticks, 1);
        for t_idx := 2 to 99
            invariant 1 <= t_idx <= 100
            invariant min_cost == (min k | 1 <= k < t_idx && 1 <= k <= 99 :: CostForT(sticks, k))
        {
            var current_cost := CostForT(sticks, t_idx);
            if current_cost < min_cost then
                min_cost := current_cost;
        }
        return min_cost;
}

predicate IsOptimalTMultiple(sticks: seq<int>, t: int)
    requires forall i :: 0 <= i < |sticks| ==> 1 <= sticks[i] <= 100
    requires 1 <= t <= 99
{
    && IsOptimalT(sticks, t)
    && CostForT(sticks, t) == CheapestCost(sticks)
}
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
    var current_min_cost := CostForT(sticks, 1);
    var current_optimal_t := 1;

    for t_iter := 2 to 99
        invariant 1 <= current_optimal_t <= 99
        invariant 1 <= t_iter <= 100
        invariant current_min_cost == CostForT(sticks, current_optimal_t)
        invariant forall k :: 1 <= k < t_iter ==> CostForT(sticks, k) >= current_min_cost
    {
        var cost_for_this_t := CostForT(sticks, t_iter);
        if cost_for_this_t < current_min_cost then
        {
            current_min_cost := cost_for_this_t;
            current_optimal_t := t_iter;
        }
    }

    t := current_optimal_t;
    min_cost := current_min_cost;

    assert 1 <= t <= 99;
    assert min_cost >= 0;
    assert min_cost == CostForT(sticks, t);

    // This assertion can be proven with the loop invariants.
    assert forall other_t :: 1 <= other_t <= 99 ==> CostForT(sticks, t) <= CostForT(sticks, other_t);
}
// </vc-code>

