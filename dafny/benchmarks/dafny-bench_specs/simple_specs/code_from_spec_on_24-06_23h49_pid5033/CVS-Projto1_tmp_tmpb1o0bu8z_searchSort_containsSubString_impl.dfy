//IMPL containsSubString
method containsSubString(a: array<char>, b: array<char>) returns (pos: int)
  requires 0 <= b.Length <= a.Length
  ensures pos == -1 || (0 <= pos <= a.Length - b.Length)
  ensures pos != -1 ==> (forall k :: 0 <= k < b.Length ==> a[pos + k] == b[k])
{
  if b.Length == 0 {
    pos := 0;
    return;
  }
  
  var i := 0;
  /* code modified by LLM (iteration 4): Fixed outer loop bounds and invariants */
  while i <= a.Length - b.Length
    invariant 0 <= i <= a.Length - b.Length + 1
    invariant forall x :: 0 <= x < i ==> exists k :: 0 <= k < b.Length && a[x + k] != b[k]
  {
    var j := 0;
    
    /* code modified by LLM (iteration 4): Simplified inner loop with correct invariants */
    while j < b.Length && a[i + j] == b[j]
      invariant 0 <= j <= b.Length
      invariant forall k :: 0 <= k < j ==> a[i + k] == b[k]
      invariant i + b.Length <= a.Length  // Safe access guaranteed by outer loop
    {
      j := j + 1;
    }
    
    /* code modified by LLM (iteration 4): Check if we found a complete match */
    if j == b.Length {
      pos := i;
      return;
    }
    
    i := i + 1;
  }
  
  pos := -1;
}