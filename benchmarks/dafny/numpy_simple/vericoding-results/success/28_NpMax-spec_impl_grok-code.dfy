// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Max(a: array<int>) returns (result: int)
    requires a.Length > 0
    ensures exists i :: 0 <= i < a.Length && result == a[i]
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= result
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Added invariant to explicitly bound max_index for verification. */
  var max_index := 0;
  result := a[0];
  var i := 1;
  while i < a.Length
    invariant 0 <= max_index < a.Length
    invariant 0 <= max_index < i
    invariant result == a[max_index]
    invariant 1 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] <= result
  {
    if a[i] > result {
      result := a[i];
      max_index := i;
    }
    i := i + 1;
  }
}
// </vc-code>
