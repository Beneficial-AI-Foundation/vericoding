// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma LinearSearchLemma(a: array<int>, e: int, idx: nat)
  requires 0 <= idx <= a.Length
  requires forall i :: 0 <= i < idx ==> a[i] != e
  ensures idx == a.Length || a[idx] == e || (forall i :: 0 <= i <= idx ==> a[i] != e)
  decreases a.Length - idx
{
  if idx < a.Length {
    if a[idx] == e {
      // Found the element
    } else {
      // Continue searching
      LinearSearchLemma(a, e, idx + 1);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method LinearSearch(a: array<int>, e: int) returns (result: nat)
    ensures result <= a.Length
    ensures result == a.Length || a[result] == e
    ensures forall i :: 0 <= i < result ==> a[i] != e
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed termination with proper decreases clause */
  result := 0;
  while result < a.Length && a[result] != e
    invariant 0 <= result <= a.Length
    invariant forall i :: 0 <= i < result ==> a[i] != e
    decreases a.Length - result
  {
    result := result + 1;
  }
}
// </vc-code>
