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
// No additional helpers needed for this implementation
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
    {
        var profit := values[i] - costs[i];
        if profit > 0 {
            sum := sum + profit;
        }
        i := i + 1;
    }
    return sum;
}
// </vc-code>

