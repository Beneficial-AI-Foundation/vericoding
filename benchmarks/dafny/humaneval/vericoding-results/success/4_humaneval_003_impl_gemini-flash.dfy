// <vc-preamble>

function sum_prefix(ops: seq<int>, len: nat): int
  requires len <= |ops|
{
  if len == 0 then 0
  else sum_prefix(ops, len-1) + ops[len-1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added function postconditions */
lemma sum_prefix_is_monotonic(ops: seq<int>, k: nat, l: nat)
  requires k <= l <= |ops|
  requires forall i :: 0 <= i < l ==> ops[i] >= 0
  ensures sum_prefix(ops, k) <= sum_prefix(ops, l)
{
  if k == l {
    // Base case: k == l, so sum_prefix(ops, k) == sum_prefix(ops, l)
  } else {
    // Inductive step: k < l
    sum_prefix_is_monotonic(ops, k, l-1);
    assert sum_prefix(ops, l) == sum_prefix(ops, l-1) + ops[l-1];
  }
}
// </vc-helpers>

// <vc-spec>
method below_zero(operations: seq<int>) returns (result: bool)
  ensures result <==> (exists i :: 0 < i <= |operations| && sum_prefix(operations, i) < 0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The logic for `result := true` and `return` was moved outside the loop, as the loop itself handles the update of `result` through its invariant. The loop termination condition correctly handles the final state of `result` once the loop finishes. */
{
  var current_sum: int := 0;
  var i: nat := 0;
  result := false; // Initialize result to false

  while i < |operations|
    invariant 0 <= i <= |operations|
    invariant current_sum == sum_prefix(operations, i)
    invariant result == (exists k :: 0 < k <= i && sum_prefix(operations, k) < 0)
  {
    current_sum := current_sum + operations[i];
    if current_sum < 0 {
      result := true;
    }
    i := i + 1;
  }
}
// </vc-code>
