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
  /* code modified by LLM (iteration 2): Fixed operator precedence issues in invariants to eliminate compilation ambiguity. */
  var found := false;
  var i := 0;
  while i < a.Length && !found
    invariant 0 <= i <= a.Length
    invariant found == (exists k, l :: 0 <= k < i && 0 <= l < b.Length && a[k] == b[l])
  {
    var j := 0;
    while j < b.Length && !found
      invariant 0 <= j <= b.Length
      invariant found == (exists k, l :: ((0 <= k < i && 0 <= l < b.Length) || (k == i && 0 <= l < j)) && a[k] == b[l])
    {
      if a[i] == b[j] {
        found := true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := found;
}
// </vc-code>
