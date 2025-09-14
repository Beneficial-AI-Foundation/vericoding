// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed placeholder helpers */
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
/* code modified by LLM (iteration 2): initialize `result` to false and properly implement loop invariants */
{
  result := false; // Initialize result to false
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result == (exists ii, jj :: 0 <= ii < i && 0 <= jj < b.Length && a[ii] == b[jj]) // Check up to the current outer loop index i-1
  {
    var j := 0;
    while j < b.Length
      invariant 0 <= j <= b.Length
      invariant result == (exists ii, jj :: (0 <= ii < i && 0 <= jj < b.Length && a[ii] == b[jj]) || (ii == i && 0 <= jj < j && a[ii] == b[jj])) // Check for a match with current a[i] up to b[j-1]
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
