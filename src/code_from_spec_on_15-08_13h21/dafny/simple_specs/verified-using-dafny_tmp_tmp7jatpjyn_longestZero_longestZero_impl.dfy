//ATOM
function getSize(i: int, j:int) : int
{
  j - i + 1  
}

//IMPL 
method longestZero(a: array<int>) returns (sz:int, pos:int)  
  requires 1 <= a.Length
  ensures 0 <= sz <= a.Length
  ensures 0 <= pos < a.Length
  ensures pos + sz <= a.Length
  ensures forall i:int :: pos <= i < pos + sz ==> a[i] == 0
  ensures forall i,j :: (0 <= i < j < a.Length && getSize(i, j) > sz) ==> exists k :: i <= k <= j && a[k] != 0
{
  sz := 0;
  pos := 0;
  
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= sz <= a.Length
    invariant 0 <= pos < a.Length
    invariant pos + sz <= a.Length
    invariant forall k:int :: pos <= k < pos + sz ==> a[k] == 0
    /* code modified by LLM (iteration 4): Changed invariant to handle all segments up to current position */
    invariant forall start, end :: (0 <= start <= end < i && forall m :: start <= m <= end ==> a[m] == 0 && getSize(start, end) > sz) ==> false
  {
    if a[i] == 0 {
      var start := i;
      var count := 0;
      /* code modified by LLM (iteration 4): Enhanced inner loop invariants */
      while i < a.Length && a[i] == 0
        invariant start <= i <= a.Length
        invariant count == i - start
        invariant forall k :: start <= k < i ==> a[k] == 0
        invariant 0 <= sz <= a.Length
        invariant 0 <= pos < a.Length
        invariant pos + sz <= a.Length
        invariant forall k:int :: pos <= k < pos + sz ==> a[k] == 0
        invariant forall s, e :: (0 <= s <= e < start && forall m :: s <= m <= e ==> a[m] == 0 && getSize(s, e) > sz) ==> false
      {
        count := count + 1;
        i := i + 1;
      }
      
      if count > sz {
        /* code modified by LLM (iteration 4): Added comprehensive assertions */
        assert forall k :: start <= k < start + count ==> a[k] == 0;
        assert count == i - start;
        assert start + count <= a.Length;
        
        sz := count;
        pos := start;
      }
    } else {
      /* code modified by LLM (iteration 4): Added assertion and helper for maintaining invariant */
      assert a[i] != 0;
      /* code modified by LLM (iteration 4): Ensure invariant holds when crossing non-zero element */
      assert forall start, end :: (0 <= start <= end <= i && forall m :: start <= m <= end ==> a[m] == 0 && getSize(start, end) > sz) ==> start > i || end < i || (start <= i <= end && a[i] != 0);
      i := i + 1;
    }
  }
}