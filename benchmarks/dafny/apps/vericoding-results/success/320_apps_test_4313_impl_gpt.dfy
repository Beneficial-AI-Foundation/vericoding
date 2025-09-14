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

// </vc-helpers>

// <vc-spec>
method solve(n: int, values: seq<int>, costs: seq<int>) returns (result: int)
    requires ValidInput(n, values, costs)
    ensures result >= 0
    ensures result == SumOfPositiveProfits(values, costs, n)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |values| == n && |costs| == n
    invariant result >= 0
    invariant result == SumOfPositiveProfits(values, costs, i)
    decreases n - i
  {
    var profit := values[i] - costs[i];
    assert SumOfPositiveProfits(values, costs, i + 1) ==
           SumOfPositiveProfits(values, costs, i) + (if profit > 0 then profit else 0);
    result := result + (if profit > 0 then profit else 0);
    i := i + 1;
  }
}
// </vc-code>

