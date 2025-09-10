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
lemma OptimalTExists(sticks: seq<int>)
    requires forall i :: 0 <= i < |sticks| ==> 1 <= sticks[i] <= 100
    ensures exists t :: 1 <= t <= 99 && IsOptimalT(sticks, t)
{
    var costs := seq(99, i requires 0 <= i < 99 => CostForT(sticks, i + 1));
    assert |costs| == 99;
    var min_cost := MinSeq(costs);
    var min_index :| 0 <= min_index < |costs| && costs[min_index] == min_cost;
    var optimal_t := min_index + 1;
    assert 1 <= optimal_t <= 99;
    assert CostForT(sticks, optimal_t) == min_cost;
    
    forall other_t | 1 <= other_t <= 99
        ensures CostForT(sticks, optimal_t) <= CostForT(sticks, other_t)
    {
        assert costs[other_t - 1] == CostForT(sticks, other_t);
        assert min_cost <= costs[other_t - 1];
    }
    
    assert IsOptimalT(sticks, optimal_t);
}

function MinSeq(s: seq<int>): int
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> MinSeq(s) <= s[i]
    ensures MinSeq(s) in s
{
    MinSeqHelper(s, 0, s[0])
}

function MinSeqHelper(s: seq<int>, index: int, current_min: int): int
    requires 0 <= index <= |s|
    requires index > 0 ==> current_min in s[..index]
    requires forall i :: 0 <= i < index ==> current_min <= s[i]
    ensures forall i :: 0 <= i < |s| ==> MinSeqHelper(s, index, current_min) <= s[i]
    ensures MinSeqHelper(s, index, current_min) in s
    decreases |s| - index
{
    if index == |s| then 
        assert current_min in s[..index];
        assert s[..index] == s;
        current_min
    else 
        var new_min := if s[index] < current_min then s[index] else current_min;
        assert new_min in s[..index+1];
        MinSeqHelper(s, index + 1, new_min)
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
    
    var i := 2;
    while i <= 99
        invariant 2 <= i <= 100
        invariant 1 <= t <= 99
        invariant min_cost >= 0
        invariant min_cost == CostForT(sticks, t)
        invariant forall j :: 1 <= j < i ==> CostForT(sticks, t) <= CostForT(sticks, j)
    {
        var current_cost := CostForT(sticks, i);
        if current_cost < min_cost {
            t := i;
            min_cost := current_cost;
        }
        i := i + 1;
    }
    
    OptimalTExists(sticks);
}
// </vc-code>

