// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Minor refactor to make it a function for better readability. */
function ComputeProfit(value: int, cost: int): int {
    var profit := value - cost;
    if profit > 0 then profit else 0
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
  /* code modified by LLM (iteration 4): Removed variable shadowing by renaming `result_var` to `current_sum` */
  var i := 0;
  var current_sum := 0;
  while i < n
    invariant 0 <= i <= n
    invariant current_sum == SumOfPositiveProfits(values, costs, i)
    invariant current_sum >= 0
  {
    current_sum := current_sum + ComputeProfit(values[i], costs[i]);
    i := i + 1;
  }
  result := current_sum;
}
// </vc-code>
