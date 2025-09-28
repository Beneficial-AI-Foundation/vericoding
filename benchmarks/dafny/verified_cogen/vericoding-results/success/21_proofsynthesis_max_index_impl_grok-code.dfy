// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MyFun1(x: array<int>) returns (max_index: int)
    requires x.Length >= 1
    ensures 0 <= max_index < x.Length
    ensures forall k :: 0 <= k < x.Length ==> x[max_index] >= x[k]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Removed duplicate var declaration for max_index, directly assigned to return parameter, and implemented loop to find max index with correct invariants */
  max_index := 0;
  var max_val := x[0];
  for i := 1 to x.Length
    invariant 0 <= max_index < x.Length
    invariant forall k :: 0 <= k < i ==> x[max_index] >= x[k]
    invariant max_val == x[max_index]
  {
    if x[i] > max_val {
      max_index := i;
      max_val := x[i];
    }
  }
}
// </vc-code>
