//IMPL 

/* code modified by LLM (iteration 4): Added complete method specification with requires/ensures clauses */
method containsSubString(a: array<char>, b: array<char>) returns (pos: int)
  requires 0 <= b.Length <= a.Length
  ensures pos == -1 || (0 <= pos <= a.Length - b.Length)
  ensures pos != -1 ==> (forall k :: 0 <= k < b.Length ==> a[pos + k] == b[k])
  ensures pos == -1 ==> (forall i :: 0 <= i <= a.Length - b.Length ==> exists j :: 0 <= j < b.Length && a[i + j] != b[j])
{
  if b.Length == 0 {
    pos := 0;
    return;
  }
  
  var i := 0;
  /* code modified by LLM (iteration 4): Fixed loop invariants to properly track no-match condition */
  while i <= a.Length - b.Length
    invariant 0 <= i <= a.Length - b.Length + 1
    invariant forall k :: 0 <= k < i ==> exists j :: 0 <= j < b.Length && a[k + j] != b[j]
  {
    var j := 0;
    
    /* code modified by LLM (iteration 4): Simplified inner loop with correct bounds and invariants */
    while j < b.Length && a[i + j] == b[j]
      invariant 0 <= j <= b.Length
      invariant forall k :: 0 <= k < j ==> a[i + k] == b[k]
      invariant i + b.Length <= a.Length
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