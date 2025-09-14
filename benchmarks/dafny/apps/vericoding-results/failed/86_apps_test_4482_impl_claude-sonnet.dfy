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
        assert sum_squares(p, a) == 0;
    } else {
        assert (p - a[0]) * (p - a[0]) >= 0;
        SumSquaresNonNegative(p, a[1..]);
        assert sum_squares(p, a[1..]) >= 0;
        assert sum_squares(p, a) == (p - a[0]) * (p - a[0]) + sum_squares(p, a[1..]);
    }
}

lemma SumSquaresMonotonic(p: int, a: seq<int>)
    ensures forall q :: q >= p ==> sum_squares(q, a) >= sum_squares(p, a) || sum_squares(q, a) <= sum_squares(p, a)
{
}

lemma OptimalExists(a: seq<int>)
    ensures exists p :: (-100 <= p <= 100 && forall q :: -100 <= q <= 100 ==> sum_squares(p, a) <= sum_squares(q, a))
{
    var min_cost := sum_squares(-100, a);
    var min_p := -100;
    
    SumSquaresNonNegative(-100, a);
    
    var p := -100;
    while p <= 100
        invariant -100 <= p <= 101
        invariant -100 <= min_p <= 100
        invariant min_cost == sum_squares(min_p, a)
        invariant forall q :: -100 <= q < p ==> sum_squares(min_p, a) <= sum_squares(q, a)
    {
        if sum_squares(p, a) < min_cost {
            min_cost := sum_squares(p, a);
            min_p := p;
        }
        p := p + 1;
    }
}

lemma FindOptimalCost(a: seq<int>) returns (cost: int, optimal_p: int)
    ensures -100 <= optimal_p <= 100
    ensures cost == sum_squares(optimal_p, a)
    ensures forall p :: -100 <= p <= 100 ==> cost <= sum_squares(p, a)
    ensures cost >= 0
{
    OptimalExists(a);
    
    var min_cost := sum_squares(-100, a);
    var min_p := -100;
    
    SumSquaresNonNegative(-100, a);
    
    var p := -100;
    while p <= 100
        invariant -100 <= p <= 101
        invariant -100 <= min_p <= 100
        invariant min_cost == sum_squares(min_p, a)
        invariant min_cost >= 0
        invariant forall q :: -100 <= q < p ==> sum_squares(min_p, a) <= sum_squares(q, a)
    {
        SumSquaresNonNegative(p, a);
        if sum_squares(p, a) < min_cost {
            min_cost := sum_squares(p, a);
            min_p := p;
        }
        p := p + 1;
    }
    
    cost := min_cost;
    optimal_p := min_p;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures IsOptimalCost(result, a)
// </vc-spec>
// <vc-code>
{
    SumSquaresNonNegative(-100, a);
    
    var min_cost := sum_squares(-100, a);
    var optimal_p := -100;
    
    var p := -99;
    while p <= 100
        invariant -99 <= p <= 101
        invariant -100 <= optimal_p <= 100
        invariant min_cost == sum_squares(optimal_p, a)
        invariant forall q :: -100 <= q < p ==> sum_squares(optimal_p, a) <= sum_squares(q, a)
        invariant min_cost >= 0
    {
        SumSquaresNonNegative(p, a);
        var current_cost := sum_squares(p, a);
        if current_cost < min_cost {
            min_cost := current_cost;
            optimal_p := p;
        }
        p := p + 1;
    }
    
    result := min_cost;
}
// </vc-code>

