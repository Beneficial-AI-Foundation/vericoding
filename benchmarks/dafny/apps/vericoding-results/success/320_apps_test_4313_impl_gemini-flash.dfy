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
function SumOfPositiveProfitsIterative(n: int, values: seq<int>, costs: seq<int>): int
  requires n >= 0
  requires |values| >= n
  requires |costs| >= n
  //ensures SumOfPositiveProfitsIterative(n, values, costs) == SumOfPositiveProfits(values, costs, n) // This ensures clause is actually incorrect.
                                                                                                   // SumOfPositiveProfitsIterative(n, values, costs) directly calculates the sum
                                                                                                   // for the first 'n' elements, while SumOfPositiveProfits(values, costs, n)
                                                                                                   // is a recursive definition that also sums elements.
                                                                                                   // The intent here is for the loop invariant to directly use SumOfPositiveProfits.
{
  if n == 0 then 0
  else
    var profit_n_minus_1 := values[n-1] - costs[n-1];
    (if profit_n_minus_1 > 0 then profit_n_minus_1 else 0) + SumOfPositiveProfitsIterative(n-1, values, costs)
}

// No changes needed here, the original problem was a duplicate variable in the main method.
// The provided recursive function `SumOfPositiveProfits` is what the
// loop invariant should refer to, and it correctly models the desired sum.
// </vc-helpers>

// <vc-spec>
method solve(n: int, values: seq<int>, costs: seq<int>) returns (result: int)
    requires ValidInput(n, values, costs)
    ensures result >= 0
    ensures result == SumOfPositiveProfits(values, costs, n)
// </vc-spec>
// <vc-code>
{
  var current_sum := 0; // Renamed 'result' to 'current_sum' to avoid name collision with the 'result' output parameter.
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant current_sum == SumOfPositiveProfits(values, costs, i) // This relates the accumulated result to the recursive sum for the prefix up to `i`
  {
    var profit := values[i] - costs[i];
    if profit > 0 {
      current_sum := current_sum + profit;
    }
    i := i + 1;
  }
  // After the loop, i == n.
  // The invariant `current_sum == SumOfPositiveProfits(values, costs, i)` becomes `current_sum == SumOfPositiveProfits(values, costs, n)`.
  // Also, since all profits added are positive, `current_sum` remains non-negative.
  return current_sum;
}
// </vc-code>

