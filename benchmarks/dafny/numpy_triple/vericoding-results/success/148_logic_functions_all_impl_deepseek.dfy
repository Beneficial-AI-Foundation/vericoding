// <vc-preamble>
// Test whether all elements in a sequence are non-zero
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed termination with proper decreases clause */

// Helper predicate that all elements from index i onwards are non-zero
predicate AllFrom(a: seq<real>, i: int)
  requires 0 <= i <= |a|
  decreases |a| - i
{
  if i >= |a| then true
  else a[i] != 0.0 && AllFrom(a, i+1)
}

// Lemma connecting the predicate to the forall condition
lemma AllFromLemma(a: seq<real>, i: int)
  requires 0 <= i <= |a|
  ensures AllFrom(a, i) == (forall j :: i <= j < |a| ==> a[j] != 0.0)
  decreases |a| - i
{
  if i < |a| {
    AllFromLemma(a, i+1);
  }
}
// </vc-helpers>

// <vc-spec>
method All(a: seq<real>) returns (result: bool)
    // The result is true if and only if all elements are non-zero
    ensures result == (forall i :: 0 <= i < |a| ==> a[i] != 0.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Simplified implementation using direct computation */
  result := true;
  var index := 0;
  while index < |a|
    invariant 0 <= index <= |a|
    invariant result == (forall j :: 0 <= j < index ==> a[j] != 0.0)
  {
    if a[index] == 0.0 {
      result := false;
      return;
    }
    index := index + 1;
  }
}
// </vc-code>
