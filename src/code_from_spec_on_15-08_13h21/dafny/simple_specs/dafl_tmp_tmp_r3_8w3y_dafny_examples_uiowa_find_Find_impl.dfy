//IMPL
method Find(a: array<int>, key: int) returns (i: int)
  /* code modified by LLM (iteration 1): removed unnecessary null check since array<int> is non-nullable */
  // if i is non-negative then 
  ensures 0 <= i ==> (// (1) i is smaller than the length of a
            i < a.Length && 
            // (2) key is at position i in a
            a[i] == key && 
            // (3) i is the smallest position where key appears
            forall k :: 0 <= k < i ==> a[k] != key
           )
  // if index is negative then
  ensures i < 0 ==> 
      // a does not contain key
      /* code modified by LLM (iteration 1): removed deprecated semicolon */
      forall k :: 0 <= k < a.Length ==> a[k] != key
{
  i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] != key
  {
    if a[i] == key {
      return;
    }
    i := i + 1;
  }
  i := -1;
}