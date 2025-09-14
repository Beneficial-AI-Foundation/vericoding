

// <vc-helpers>
module VC_Helpers { }
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
    invariant forall ii :: 0 <= ii < i ==> forall j0 :: 0 <= j0 < b.Length ==> a[ii] != b[j0]
    decreases a.Length - i
  {
    var j := 0;
    while j < b.Length
      invariant 0 <= j <= b.Length
      invariant 0 <= i < a.Length
      invariant forall jj :: 0 <= jj < j ==> a[i] != b[jj]
      invariant forall ii :: 0 <= ii < i ==> forall j0 :: 0 <= j0 < b.Length ==> a[ii] != b[j0]
      decreases b.Length - j
    {
      if a[i] == b[j] {
        result := true;
        assert exists i0:int, j0:int :: i0 == i && j0 == j && 0 <= i0 < a.Length && 0 <= j0 < b.Length && a[i0] == b[j0];
        return;
      }
      j := j + 1;
    }
    assert j == b.Length;
    assert forall j0 :: 0 <= j0 < b.Length ==> a[i] != b[j0];
    var oldI := i;
    assert forall ii :: 0 <= ii < oldI ==> forall j0 :: 0 <= j0 < b.Length ==> a[ii] != b[j0];
    i := i + 1;
    forall ii | 0 <= ii < i
      ensures forall j0 :: 0 <= j0 < b.Length ==> a[ii] != b[j0]
    {
      if ii < oldI {
        assert forall j0 :: 0 <= j0 < b.Length ==> a[ii] != b[j0];
      } else {
        assert ii == oldI;
        assert forall j0 :: 0 <= j0 < b.Length ==> a[ii] != b[j0];
      }
    }
  }
  result := false;
}
// </vc-code>

