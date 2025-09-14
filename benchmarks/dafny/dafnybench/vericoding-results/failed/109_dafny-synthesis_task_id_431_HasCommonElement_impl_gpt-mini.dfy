

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    requires a != null && b != null
    ensures result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j]
    ensures !result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> a[i] != b[j]
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall i0, j0 :: 0 <= i0 < i && 0 <= j0 < b.Length ==> a[i0] != b[j0]
  {
    var j := 0;
    while j < b.Length
      invariant 0 <= j <= b.Length
      invariant 0 <= i < a.Length
      invariant forall j0 :: 0 <= j0 < j ==> a[i] != b[j0]
    {
      if a[i] == b[j] {
        result := true;
        assert exists i0, j0 :: 0 <= i0 < a.Length && 0 <= j0 < b.Length && a[i0] == b[j0];
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := false;
  assert i == a.Length;
  assert forall i0, j0 :: 0 <= i0 < a.Length && 0 <= j0 < b.Length ==> a[i0] != b[j0];
}
// </vc-code>

