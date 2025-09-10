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
lemma Lemma_CostForT_Min(sticks: seq<int>, t: int, min_cost: int)
    requires forall i :: 0 <= i < |sticks| ==> 1 <= sticks[i] <= 100
    requires 1 <= t <= 99
    requires min_cost >= 0
    requires min_cost == CostForT(sticks, t)
    requires forall other_t :: 1 <= other_t <= 99 ==> min_cost <= CostForT(sticks, other_t)
    ensures IsOptimalT(sticks, t)
{
}

lemma Lemma_CostForT_Range(sticks: seq<int>, t: int)
    requires forall i :: 0 <= i < |sticks| ==> 1 <= sticks[i] <= 100
    requires 1 <= t <= 99
    ensures CostForT(sticks, t) >= 0
{
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
    var cost: int;
    min_cost := 1000000;
    t := 1;
    var i := 1;
    while i <= 99
        invariant 1 <= i <= 100
        invariant 1 <= t <= 99
        invariant min_cost >= 0
        invariant min_cost == CostForT(sticks, t)
        invariant forall j :: 1 <= j < i ==> min_cost <= CostForT(sticks, j)
    {
        cost := CostForT(sticks, i);
        Lemma_CostForT_Range(sticks, i);
        if cost < min_cost {
            min_cost := cost;
            t := i;
        }
        i := i + 1;
    }
    Lemma_CostForT_Min(sticks, t, min_cost);
}
// </vc-code>

