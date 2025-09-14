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
lemma SumSquaresNonNegative(p: int, a: seq<int>)
    ensures sum_squares(p, a) >= 0
{
    if |a| == 0 {
    } else {
        SumSquaresNonNegative(p, a[1..]);
        assert (p - a[0]) * (p - a[0]) >= 0;
        assert sum_squares(p, a) == (p - a[0]) * (p - a[0]) + sum_squares(p, a[1..]);
    }
}

lemma MinCostMaintainsInvariant(p: int, a: seq<int>, minCost: int, cost: int)
    requires -100 <= p <= 100
    requires ValidInput(|a|, a)
    requires minCost >= 0
    requires forall k :: -100 <= k < p ==> minCost <= sum_squares(k, a)
    requires exists k :: -100 <= k < p+1 && minCost == sum_squares(k, a)
    requires cost == sum_squares(p, a)
    ensures cost < minCost ==> forall k :: -100 <= k < p+1 ==> minCost <= sum_squares(k, a)
    ensures cost >= minCost ==> forall k :: -100 <= k < p+1 ==> minCost <= sum_squares(k, a)
{
    if cost < minCost {
        forall k | -100 <= k < p+1
            ensures minCost <= sum_squares(k, a)
        {
            if k == p {
                assert minCost == cost == sum_squares(k, a);
            } else {
                assert k < p;
            }
        }
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
    var minCost := sum_squares(-100, a);
    SumSquaresNonNegative(-100, a);
    for p := -99 to 100
        invariant minCost >= 0
        invariant forall k :: -100 <= k < p ==> minCost <= sum_squares(k, a)
        invariant exists k :: -100 <= k < p+1 && minCost == sum_squares(k, a)
    {
        SumSquaresNonNegative(p, a);
        var cost := sum_squares(p, a);
        if cost < minCost {
            minCost := cost;
            MinCostMaintainsInvariant(p, a, minCost, cost);
        }
    }
    result := minCost;
}
// </vc-code>

