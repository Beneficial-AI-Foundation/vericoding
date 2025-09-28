// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 2): Initialize result and fix loop invariants */
  result := false;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant !result
    invariant forall i', j :: 0 <= i' < i && 0 <= j < b.Length ==> a[i'] != b[j]
  {
    var j := 0;
    while j < b.Length
      invariant 0 <= j <= b.Length
      invariant forall j' :: 0 <= j' < j ==> a[i] != b[j']
    {
      if a[i] == b[j] {
        result := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := false;
}
// </vc-code>
