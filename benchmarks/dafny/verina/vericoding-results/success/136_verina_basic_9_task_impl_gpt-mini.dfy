// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): predicate to check membership in array */
predicate InArray(arr: array<int>, x: int) reads arr { exists i :: 0 <= i < arr.Length && arr[i] == x }
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
  /* code modified by LLM (iteration 2): iterate arrays and return on first match */
  var i := 0;
  while i < a.Length
    decreases a.Length - i
    invariant 0 <= i <= a.Length
    invariant forall i0 :: 0 <= i0 < i ==> forall j0 :: 0 <= j0 < b.Length ==> a[i0] != b[j0]
  {
    var j := 0;
    while j < b.Length
      decreases b.Length - j
      invariant 0 <= j <= b.Length
      invariant forall j0 :: 0 <= j0 < j ==> a[i] != b[j0]
    {
      if a[i] != b[j] {
        j := j + 1;
      } else {
        result := true;
        return;
      }
    }
    // no match for this i
    assert forall j0 :: 0 <= j0 < b.Length ==> a[i] != b[j0];
    i := i + 1;
  }
  assert forall i0 :: 0 <= i0 < a.Length ==> forall j0 :: 0 <= j0 < b.Length ==> a[i0] != b[j0];
  result := false;
}
// </vc-code>
