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
  ensures SumOfPositiveProfitsIterative(n, values, costs) == SumOfPositiveProfits(values, costs, n)
{
  if n == 0 then 0
  else
    var profit_n_minus_1 := values[n-1] - costs[n-1];
    (if profit_n_minus_1 > 0 then profit_n_minus_1 else 0) + SumOfPositiveProfitsIterative(n-1, values, costs)
}

// Proof that the iterative function is equivalent to the recursive one - not strictly necessary as Dafny's SMT solver can often infer this if the iterative version is directly used in the loop invariant.
// However, explicitly proving equivalence can sometimes help guide the verifier or be useful for complex recursive definitions.
// In this specific case, the loop invariant directly mirrors the recursive definition, making this lemma less crucial for verification success.

/*
lemma SumOfPositiveProfitsEquivalent(values: seq<int>, costs: seq<int>, n: int)
    requires |values| >= n
    requires |costs| >= n
    requires n >= 0
    ensures SumOfPositiveProfits(values, costs, n) == SumOfPositiveProfitsIterative(n, values, costs)
{
    if n == 0 {
        // Base case: 0 == 0
    } else {
        SumOfPositiveProfitsEquivalent(values, costs, n-1);
    }
}
*/
// </vc-helpers>

// <vc-spec>
method solve(n: int, values: seq<int>, costs: seq<int>) returns (result: int)
    requires ValidInput(n, values, costs)
    ensures result >= 0
    ensures result == SumOfPositiveProfits(values, costs, n)
// </vc-spec>
// <vc-code>
{
  var result := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result == SumOfPositiveProfits(values, costs, i) // This relates the accumulated result to the recursive sum for the prefix up to `i`
  {
    var profit := values[i] - costs[i];
    if profit > 0 {
      result := result + profit;
    }
    i := i + 1;
  }
  // After the loop, i == n.
  // The invariant `result == SumOfPositiveProfits(values, costs, i)` becomes `result == SumOfPositiveProfits(values, costs, n)`.
  // Also, since all profits added are positive, `result` remains non-negative.
  return result;
}
// </vc-code>

