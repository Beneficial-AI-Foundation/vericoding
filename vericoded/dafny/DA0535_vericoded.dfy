function SumOfPositiveProfits(values: seq<int>, costs: seq<int>, n: int): int
    requires |values| >= n
    requires |costs| >= n
    requires n >= 0
{
    if n == 0 then 0
    else 
        var profit := values[n-1] - costs[n-1];
        SumOfPositiveProfits(values, costs, n-1) + (if profit > 0 then profit else 0)
}

predicate ValidInput(n: int, values: seq<int>, costs: seq<int>)
{
    |values| == n && |costs| == n && n >= 0
}

// <vc-helpers>
lemma SumOfPositiveProfitsIterative(values: seq<int>, costs: seq<int>, n: int)
    requires |values| >= n
    requires |costs| >= n
    requires n >= 0
    ensures SumOfPositiveProfits(values, costs, n) == SumOfPositiveProfitsIter(values, costs, n)
{
    if n == 0 {
        // Base case: both return 0
    } else {
        // Inductive case
        SumOfPositiveProfitsIterative(values, costs, n-1);
        // Now we know SumOfPositiveProfits(values, costs, n-1) == SumOfPositiveProfitsIter(values, costs, n-1)
        
        var profit := values[n-1] - costs[n-1];
        var profitContribution := if profit > 0 then profit else 0;
        
        // By definition:
        // SumOfPositiveProfits(values, costs, n) = SumOfPositiveProfits(values, costs, n-1) + profitContribution
        // SumOfPositiveProfitsIter(values, costs, n) = SumOfPositiveProfitsIter(values, costs, n-1) + profitContribution
        // Since the first n-1 parts are equal by induction, the full sums are equal
    }
}

function SumOfPositiveProfitsIter(values: seq<int>, costs: seq<int>, n: int): int
    requires |values| >= n
    requires |costs| >= n
    requires n >= 0
{
    if n == 0 then 0
    else
        var profit := values[n-1] - costs[n-1];
        SumOfPositiveProfitsIter(values, costs, n-1) + (if profit > 0 then profit else 0)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, values: seq<int>, costs: seq<int>) returns (result: int)
    requires ValidInput(n, values, costs)
    ensures result >= 0
    ensures result == SumOfPositiveProfits(values, costs, n)
// </vc-spec>
// <vc-code>
{
    var sum := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant sum == SumOfPositiveProfits(values, costs, i)
        invariant sum >= 0
    {
        var profit := values[i] - costs[i];
        if profit > 0 {
            sum := sum + profit;
        }
        i := i + 1;
    }
    
    result := sum;
}
// </vc-code>

