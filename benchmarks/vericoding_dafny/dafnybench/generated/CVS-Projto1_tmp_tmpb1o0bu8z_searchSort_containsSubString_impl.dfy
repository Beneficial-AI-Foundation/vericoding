// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method containsSubString(a: array<char>, b: array<char>) returns (pos: int)
    requires 0 <= b.Length <= a.Length
// </vc-spec>
// <vc-code>
{
  if b.Length == 0 {
    pos := 0;
    return;
  }
  
  var i := 0;
  while i <= a.Length - b.Length
    invariant 0 <= i <= a.Length - b.Length + 1
  {
    var j := 0;
    var found := true;
    
    while j < b.Length && found
      invariant 0 <= j <= b.Length
      invariant found ==> forall k :: 0 <= k < j ==> a[i + k] == b[k]
    {
      if a[i + j] != b[j] {
        found := false;
      }
      j := j + 1;
    }
    
    if found {
      pos := i;
      return;
    }
    
    i := i + 1;
  }
  
  pos := -1;
}
// </vc-code>