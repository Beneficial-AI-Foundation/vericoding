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

lemma SumCriminalsCaughtAccumulation(n: int, a_idx: int, x: seq<int>, distance: int)
    requires n > 0
    requires 0 <= a_idx < n
    requires |x| == n
    requires forall i :: 0 <= i < n ==> (x[i] == 0 || x[i] == 1)
    requires 1 <= distance < n
    ensures x[a_idx] + SumCriminalsCaught(n, a_idx, x, 1) == 
            x[a_idx] + SumFromDistance1(n, a_idx, x, distance) + SumCriminalsCaught(n, a_idx, x, distance + 1)
{
    // Helper lemma for accumulation property
}

function SumFromDistance1(n: int, a_idx: int, x: seq<int>, up_to: int): int
    requires n > 0
    requires 0 <= a_idx < n
    requires |x| == n
    requires forall i :: 0 <= i < n ==> (x[i] == 0 || x[i] == 1)
    requires 1 <= up_to <= n
    decreases up_to
{
    if up_to == 1 then
        var le := a_idx - 1;
        var rg := a_idx + 1;
        var le_valid := le >= 0 && le < n;
        var rg_valid := rg >= 0 && rg < n;
        if !le_valid && !rg_valid then 0
        else if le_valid && !rg_valid then x[le]
        else if !le_valid && rg_valid then x[rg]
        else if le_valid && rg_valid && x[le] == 1 && x[rg] == 1 then 2
        else 0
    else
        var current := SumFromDistance1(n, a_idx, x, up_to - 1);
        var le := a_idx - up_to;
        var rg := a_idx + up_to;
        var le_valid := le >= 0 && le < n;
        var rg_valid := rg >= 0 && rg < n;
        var add :=
            if !le_valid && !rg_valid then 0
            else if le_valid && !rg_valid then x[le]
            else if !le_valid && rg_valid then x[rg]
            else if le_valid && rg_valid && x[le] == 1 && x[rg] == 1 then 2
            else 0;
        current + add
}

lemma SumRelation(n: int, a_idx: int, x: seq<int>, distance: int)
    requires n > 0
    requires 0 <= a_idx < n
    requires |x| == n
    requires forall i :: 0 <= i < n ==> (x[i] == 0 || x[i] == 1)
    requires 1 <= distance <= n
    ensures SumFromDistance1(n, a_idx, x, distance) + SumCriminalsCaught(n, a_idx, x, distance + 1) ==
            SumCriminalsCaught(n, a_idx, x, 1)
{
    // Proves the relationship between accumulated sum and recursive sum
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
    result := x[a_idx];
    
    var accumulated := 0;
    var distance := 1;
    
    while distance <= n
        invariant 1 <= distance <= n + 1
        invariant result >= 0
        invariant accumulated >= 0
        invariant result == x[a_idx] + accumulated + SumCriminalsCaught(n, a_idx, x, distance)
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
        
        if !le_valid && !rg_valid {
            distance := n + 1;
        } else {
            accumulated := accumulated + current_caught;
            distance := distance + 1;
        }
    }
    
    result := x[a_idx] + accumulated;
}
// </vc-code>

