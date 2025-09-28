// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause */
predicate OnlyOneDistinct(a: array<int>) 
  reads a
{
  forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j]
}
// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
    requires a.Length > 0
    ensures result ==> (forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j])
    ensures !result ==> (exists i :: 0 <= i < a.Length && a[i] != a[0])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed loop invariants and post-conditions */
{
  if a.Length == 1 {
    return true;
  }

  var firstElement := a[0];
  var foundDifferent := false;
  for i := 1 to a.Length
    invariant 0 <= i <= a.Length
    invariant !foundDifferent ==> (forall k :: 0 <= k < i ==> a[k] == firstElement)
  {
    if a[i] != firstElement {
      foundDifferent := true;
      break;
    }
  }

  result := !foundDifferent;
}
// </vc-code>
