predicate ValidInput(n: int, a: int, x: seq<int>)
{
    n > 0 && 1 <= a <= n && |x| == n && 
    forall i :: 0 <= i < n ==> (x[i] == 0 || x[i] == 1)
}

function SumCriminalsCaught(n: int, a_idx: int, x: seq<int>, distance: int): int
    requires n > 0
    requires 0 <= a_idx < n
    requires |x| == n
    requires forall i :: 0 <= i < n ==> (x[i] == 0 || x[i] == 1)
    requires distance >= 1
    decreases n + 1 - distance
    ensures SumCriminalsCaught(n, a_idx, x, distance) >= 0
{
    if distance > n then 0
    else
        var le := a_idx - distance;
        var rg := a_idx + distance;
        var le_valid := le >= 0 && le < n;
        var rg_valid := rg >= 0 && rg < n;
        var current_caught :=
            if !le_valid && !rg_valid then 0
            else if le_valid && !rg_valid then x[le]
            else if !le_valid && rg_valid then x[rg]
            else if le_valid && rg_valid && x[le] == 1 && x[rg] == 1 then 2
            else 0;
        if !le_valid && !rg_valid then current_caught
        else current_caught + SumCriminalsCaught(n, a_idx, x, distance + 1)
}

function TotalCriminalsCaught(n: int, a: int, x: seq<int>): int
    requires ValidInput(n, a, x)
{
    x[a-1] + SumCriminalsCaught(n, a-1, x, 1)
}

// <vc-helpers>
lemma SumCriminalsCaughtNonNegative(n: int, a_idx: int, x: seq<int>, distance: int)
    requires n > 0
    requires 0 <= a_idx < n
    requires |x| == n
    requires forall i :: 0 <= i < n ==> (x[i] == 0 || x[i] == 1)
    requires distance >= 1
    ensures SumCriminalsCaught(n, a_idx, x, distance) >= 0
{
    // This follows from the ensures clause of the function itself
}

lemma SumCriminalsCaughtDecomposition(n: int, a_idx: int, x: seq<int>, distance: int)
    requires n > 0
    requires 0 <= a_idx < n
    requires |x| == n
    requires forall i :: 0 <= i < n ==> (x[i] == 0 || x[i] == 1)
    requires 1 <= distance <= n
    ensures SumCriminalsCaught(n, a_idx, x, 1) == 
            AccumulatedSum(n, a_idx, x, 1, distance) + SumCriminalsCaught(n, a_idx, x, distance + 1)
    decreases n - distance
{
    if distance == n {
        calc {
            SumCriminalsCaught(n, a_idx, x, 1);
            == AccumulatedSum(n, a_idx, x, 1, n) + SumCriminalsCaught(n, a_idx, x, n + 1);
            == AccumulatedSum(n, a_idx, x, 1, n) + 0;
        }
    } else if distance == 1 {
        assert AccumulatedSum(n, a_idx, x, 1, 0) == 0;
    } else {
        SumCriminalsCaughtDecomposition(n, a_idx, x, distance - 1);
    }
}

function AccumulatedSum(n: int, a_idx: int, x: seq<int>, from: int, to: int): int
    requires n > 0
    requires 0 <= a_idx < n
    requires |x| == n
    requires forall i :: 0 <= i < n ==> (x[i] == 0 || x[i] == 1)
    requires 1 <= from <= to + 1 <= n + 1
    decreases to - from + 1
{
    if from > to then 0
    else 
        var le := a_idx - from;
        var rg := a_idx + from;
        var le_valid := le >= 0 && le < n;
        var rg_valid := rg >= 0 && rg < n;
        var current :=
            if !le_valid && !rg_valid then 0
            else if le_valid && !rg_valid then x[le]
            else if !le_valid && rg_valid then x[rg]
            else if le_valid && rg_valid && x[le] == 1 && x[rg] == 1 then 2
            else 0;
        current + AccumulatedSum(n, a_idx, x, from + 1, to)
}

lemma AccumulatedSumProperty(n: int, a_idx: int, x: seq<int>, from: int, to: int)
    requires n > 0
    requires 0 <= a_idx < n
    requires |x| == n
    requires forall i :: 0 <= i < n ==> (x[i] == 0 || x[i] == 1)
    requires 1 <= from <= to <= n
    ensures AccumulatedSum(n, a_idx, x, from, to) >= 0
{
    // Follows from the fact that each term is non-negative
}

lemma AccumulatedSumExtension(n: int, a_idx: int, x: seq<int>, from: int, to: int)
    requires n > 0
    requires 0 <= a_idx < n
    requires |x| == n
    requires forall i :: 0 <= i < n ==> (x[i] == 0 || x[i] == 1)
    requires 1 <= from <= to < n
    ensures AccumulatedSum(n, a_idx, x, from, to + 1) == 
            AccumulatedSum(n, a_idx, x, from, to) + 
            (var d := to + 1;
             var le := a_idx - d;
             var rg := a_idx + d;
             var le_valid := le >= 0 && le < n;
             var rg_valid := rg >= 0 && rg < n;
             if !le_valid && !rg_valid then 0
             else if le_valid && !rg_valid then x[le]
             else if !le_valid && rg_valid then x[rg]
             else if le_valid && rg_valid && x[le] == 1 && x[rg] == 1 then 2
             else 0)
{
    // Direct from definition
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, x: seq<int>) returns (result: int)
    requires ValidInput(n, a, x)
    ensures result >= 0
    ensures result == TotalCriminalsCaught(n, a, x)
// </vc-spec>
// <vc-code>
{
    var a_idx := a - 1;
    var accumulated := 0;
    var distance := 1;
    result := x[a_idx];
    
    while distance <= n
        invariant 1 <= distance <= n + 1
        invariant accumulated == AccumulatedSum(n, a_idx, x, 1, distance - 1)
        invariant result == x[a_idx] + accumulated
        invariant accumulated >= 0
    {
        var le := a_idx - distance;
        var rg := a_idx + distance;
        var le_valid := le >= 0 && le < n;
        var rg_valid := rg >= 0 && rg < n;
        
        var current_caught :=
            if !le_valid && !rg_valid then 0
            else if le_valid && !rg_valid then x[le]
            else if !le_valid && rg_valid then x[rg]
            else if le_valid && rg_valid && x[le] == 1 && x[rg] == 1 then 2
            else 0;
        
        accumulated := accumulated + current_caught;
        distance := distance + 1;
    }
    
    assert distance == n + 1;
    assert accumulated == AccumulatedSum(n, a_idx, x, 1, n);
    SumCriminalsCaughtDecomposition(n, a_idx, x, n);
    assert SumCriminalsCaught(n, a_idx, x, 1) == accumulated + SumCriminalsCaught(n, a_idx, x, n + 1);
    assert SumCriminalsCaught(n, a_idx, x, n + 1) == 0;
    assert result == x[a_idx] + SumCriminalsCaught(n, a_idx, x, 1);
}
// </vc-code>

