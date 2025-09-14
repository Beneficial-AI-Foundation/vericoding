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
        // Base case: sum_squares(p, []) = 0 >= 0
    } else {
        // Inductive case: (p - a[0])^2 >= 0 and sum_squares(p, a[1..]) >= 0
        SumSquaresNonNegative(p, a[1..]);
        // Therefore sum_squares(p, a) >= 0
    }
}

lemma OptimalExists(a: seq<int>)
    ensures exists p :: -100 <= p <= 100 && 
                       (forall q :: -100 <= q <= 100 ==> sum_squares(p, a) <= sum_squares(q, a))
{
    // We'll prove existence by showing that the minimum over the finite set exists
    var minVal := sum_squares(-100, a);
    var minP := -100;
    var i := -99;
    
    while i <= 100
        invariant -99 <= i <= 101
        invariant -100 <= minP <= 100
        invariant minP <= i - 1 || minP == -100
        invariant minVal == sum_squares(minP, a)
        invariant forall j :: -100 <= j < i ==> minVal <= sum_squares(j, a)
    {
        if sum_squares(i, a) < minVal {
            minVal := sum_squares(i, a);
            minP := i;
        }
        i := i + 1;
    }
    
    // Now minP is the optimal p
    assert minP >= -100 && minP <= 100;
    assert forall q :: -100 <= q <= 100 ==> sum_squares(minP, a) <= sum_squares(q, a);
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures IsOptimalCost(result, a)
// </vc-spec>
// <vc-code>
{
    OptimalExists(a);
    
    var minCost := sum_squares(-100, a);
    var optimalP := -100;
    var p := -99;
    
    while p <= 100
        invariant -99 <= p <= 101
        invariant -100 <= optimalP <= 100
        invariant optimalP < p || (optimalP == -100 && p == -99)
        invariant minCost == sum_squares(optimalP, a)
        invariant forall q :: -100 <= q < p ==> minCost <= sum_squares(q, a)
    {
        var currentCost := sum_squares(p, a);
        if currentCost < minCost {
            minCost := currentCost;
            optimalP := p;
        }
        p := p + 1;
    }
    
    SumSquaresNonNegative(optimalP, a);
    assert minCost >= 0;
    assert -100 <= optimalP <= 100;
    assert minCost == sum_squares(optimalP, a);
    assert forall q :: -100 <= q <= 100 ==> minCost <= sum_squares(q, a);
    
    result := minCost;
}
// </vc-code>

