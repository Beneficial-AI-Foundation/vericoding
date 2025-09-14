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
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant !(exists ii, jj :: 0 <= ii < i && 0 <= jj < b.Length && a[ii] == b[jj])
  {
    var j := 0;
    while j < b.Length
      invariant 0 <= j <= b.Length
      invariant !(exists jj :: 0 <= jj < j && a[i] == b[jj])
    {
      if a[i] == b[j] {
        return true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>
