// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma AllEqualToFirst(a: array<int>, first: int)
  requires a.Length > 0
  requires forall i :: 0 <= i < a.Length ==> a[i] == first
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j]
{
}
// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
    requires a.Length > 0
    ensures result ==> (forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j])
    ensures !result ==> (exists i :: 0 <= i < a.Length && a[i] != a[0])
// </vc-spec>
// <vc-code>
{
  var first := a[0];
  var index := 0;
  
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant forall i :: 0 <= i < index ==> a[i] == first
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
