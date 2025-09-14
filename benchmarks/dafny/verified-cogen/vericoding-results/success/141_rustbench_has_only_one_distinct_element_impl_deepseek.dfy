// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
lemma DistinctElementLemma(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  ensures a[i] == a[j] || a[i] != a[j]
{
}

predicate AllElementsEqual(a: array<int>, start: int, end: int)
  requires 0 <= start <= end <= a.Length
  reads a
  ensures AllElementsEqual(a, start, end) ==> forall k, l :: start <= k < end && start <= l < end ==> a[k] == a[l]
  decreases end - start
{
  if start == end then
    true
  else
    (forall k :: start <= k < end ==> a[k] == a[start]) && AllElementsEqual(a, start + 1, end)
}
// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
    ensures result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j]
    ensures !result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] != a[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed termination proof */
{
  if a.Length <= 1 {
    result := true;
    return;
  }
  
  var first := a[0];
  var index := 1;
  
  while index < a.Length
    invariant 1 <= index <= a.Length
    invariant forall i :: 0 <= i < index ==> a[i] == first
    decreases a.Length - index
  {
    if a[index] != first {
      result := false;
      return;
    }
    index := index + 1;
  }
  
  result := true;
}
// </vc-code>
