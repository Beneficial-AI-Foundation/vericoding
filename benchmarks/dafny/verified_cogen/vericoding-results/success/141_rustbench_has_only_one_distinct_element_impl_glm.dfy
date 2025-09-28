// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
    ensures result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j]
    ensures !result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] != a[j]
// </vc-spec>
// <vc-code>
{
  if a.Length == 0 { return true; }
  var first := a[0];
  for i := 1 to a.Length
    invariant forall k :: 0 <= k < i ==> a[k] == first
  {
    if a[i] != first { return false; }
  }
  return true;
}
// </vc-code>
