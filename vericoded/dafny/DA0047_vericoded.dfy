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
lemma CostForTNonNegative(sticks: seq<int>, t: int)
    requires forall i :: 0 <= i < |sticks| ==> 1 <= sticks[i] <= 100
    requires 1 <= t <= 99
    ensures CostForT(sticks, t) >= 0
{
    // This follows from the ensures clause of CostForT
}

lemma OptimalTExists(sticks: seq<int>) returns (optimal_t: int)
    requires forall i :: 0 <= i < |sticks| ==> 1 <= sticks[i] <= 100
    ensures 1 <= optimal_t <= 99
    ensures IsOptimalT(sticks, optimal_t)
{
    var min_t := 1;
    var min_cost := CostForT(sticks, 1);
    
    for candidate_t := 2 to 100
        invariant 1 <= min_t <= 99
        invariant min_cost == CostForT(sticks, min_t)
        invariant forall t :: 1 <= t < candidate_t && t <= 99 ==> CostForT(sticks, min_t) <= CostForT(sticks, t)
    {
        if candidate_t <= 99 {
            var candidate_cost := CostForT(sticks, candidate_t);
            if candidate_cost < min_cost {
                min_cost := candidate_cost;
                min_t := candidate_t;
            }
        }
    }
    
    optimal_t := min_t;
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
    t := 1;
    min_cost := CostForT(sticks, 1);
    
    var current_t := 2;
    while current_t <= 99
        invariant 1 <= t <= 99
        invariant 2 <= current_t <= 100
        invariant min_cost == CostForT(sticks, t)
        invariant min_cost >= 0
        invariant forall other_t :: 1 <= other_t < current_t && other_t <= 99 ==> 
            CostForT(sticks, t) <= CostForT(sticks, other_t)
    {
        var current_cost := CostForT(sticks, current_t);
        if current_cost < min_cost {
            min_cost := current_cost;
            t := current_t;
        }
        current_t := current_t + 1;
    }
    
    assert current_t == 100;
    assert forall other_t :: 1 <= other_t <= 99 ==> 
        CostForT(sticks, t) <= CostForT(sticks, other_t);
}
// </vc-code>

