// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma NoOpHelper() ensures true { }
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
  result := false;
  while i < a.Length
    decreases a.Length - i
    invariant 0 <= i <= a.Length
    invariant !result ==> (forall ii, jj :: 0 <= ii < i && 0 <= jj < b.Length ==> a[ii] != b[jj])
    invariant result ==> (exists ii, jj :: 0 <= ii < a.Length && 0 <= jj < b.Length && a[ii] == b[jj])
  {
    var j := 0;
    while j < b.Length
      decreases b.Length - j
      invariant 0 <= j <= b.Length
      invariant !result ==> (forall jj0 :: 0 <= jj0 < j ==> a[i] != b[jj0])
      invariant result ==> (exists ii, jj :: 0 <= ii < a.Length && 0 <= jj < b.Length && a[ii] == b[jj])
    {
      if a[i] == b[j] {
        result := true;
        break;
      }
      j := j + 1;
    }
    if result { break; }
    i := i + 1;
  }
}
// </vc-code>
