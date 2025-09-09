//IMPL 
method Partition(a: array<int>) returns (lo: int, hi: int)
  modifies a
  ensures 0 <= lo <= hi <= a.Length
  ensures forall x | 0 <= x < lo :: a[x] < 0
  ensures forall x | lo <= x < hi :: a[x] == 0
  ensures forall x | hi <= x < a.Length :: a[x] > 0
{
  /* code modified by LLM (iteration 1): Rewrote the partitioning algorithm using a simpler three-pointer approach with proper invariants */
  lo := 0;
  hi := a.Length;
  var i := 0;
  
  while i < hi
    invariant 0 <= lo <= i <= hi <= a.Length
    invariant forall x | 0 <= x < lo :: a[x] < 0
    invariant forall x | lo <= x < i :: a[x] == 0
    invariant forall x | hi <= x < a.Length :: a[x] > 0
    decreases hi - i
  {
    if a[i] < 0 {
      /* code modified by LLM (iteration 1): Swap negative element to front and increment both lo and i */
      a[i], a[lo] := a[lo], a[i];
      lo := lo + 1;
      i := i + 1;
    } else if a[i] == 0 {
      /* code modified by LLM (iteration 1): Zero is already in correct position, just move forward */
      i := i + 1;
    } else {
      /* code modified by LLM (iteration 1): Swap positive element to back, decrement hi but don't increment i since we need to process the swapped element */
      hi := hi - 1;
      a[i], a[hi] := a[hi], a[i];
    }
  }
}