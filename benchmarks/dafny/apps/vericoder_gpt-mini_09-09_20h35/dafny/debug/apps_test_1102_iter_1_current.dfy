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
// No auxiliary helpers required for this solution.
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, x: seq<int>) returns (result: int)
    requires ValidInput(n, a, x)
    ensures result >= 0
    ensures result == TotalCriminalsCaught(n, a, x)
// </vc-spec>
// <vc-code>
{
  result := TotalCriminalsCaught(n, a, x);
}
// </vc-code>

