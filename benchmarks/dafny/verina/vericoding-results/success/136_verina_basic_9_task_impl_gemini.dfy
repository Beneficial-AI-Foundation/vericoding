// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsInArray(x: int, arr: array<int>)
  reads arr
{
  exists i :: 0 <= i < arr.Length && arr[i] == x
}
// </vc-helpers>

// <vc-spec>
method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    requires 
        a.Length > 0 &&
        b.Length > 0
    ensures
        result == (exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j])
// </vc-spec>
// <vc-code>
{
  result := false;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result <==> (exists k :: 0 <= k < i && IsInArray(a[k], b))
  {
    var j := 0;
    while j < b.Length
      invariant 0 <= j <= b.Length
      invariant forall l :: 0 <= l < j ==> a[i] != b[l]
    {
      if a[i] == b[j] {
        result := true;
        assert IsInArray(a[i], b);
        return;
      }
      j := j + 1;
    }
    assert forall l :: 0 <= l < b.Length ==> a[i] != b[l];
    assert !IsInArray(a[i], b);
    i := i + 1;
  }
}
// </vc-code>
