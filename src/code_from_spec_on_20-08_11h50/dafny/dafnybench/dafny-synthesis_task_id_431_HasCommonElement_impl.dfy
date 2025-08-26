method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    requires a != null && b != null
    ensures result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j]
    ensures !result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> a[i] != b[j]
// </vc-spec>
// <vc-code>
{
  result := false;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant !result ==> forall ii, j :: 0 <= ii < i && 0 <= j < b.Length ==> a[ii] != b[j]
    invariant result ==> exists ii, j :: 0 <= ii < a.Length && 0 <= j < b.Length && a[ii] == b[j]
  {
    var j := 0;
    while j < b.Length
      invariant 0 <= j <= b.Length
      invariant !result ==> forall jj :: 0 <= jj < j ==> a[i] != b[jj]
      invariant !result ==> forall ii, jj :: 0 <= ii < i && 0 <= jj < b.Length ==> a[ii] != b[jj]
      invariant result ==> exists ii, jj :: 0 <= ii < a.Length && 0 <= jj < b.Length && a[ii] == b[jj]
    {
      if a[i] == b[j] {
        result := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>