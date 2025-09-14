// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    requires a != null && b != null
    ensures result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j]
    ensures !result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> a[i] != b[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Re-implemented with nested loops to see if it bypasses the compilation warning issue. */
  result := false;
  var i: nat := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant !result ==> forall k, l :: 0 <= k < i && 0 <= l < b.Length ==> a[k] != b[l]
  {
    var j: nat := 0;
    while j < b.Length
      invariant 0 <= j <= b.Length
      invariant !result ==> forall k, l :: 0 <= k < i && 0 <= l < b.Length ==> a[k] != b[l]
      invariant !result ==> forall l :: 0 <= l < j ==> a[i] != b[l]
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
