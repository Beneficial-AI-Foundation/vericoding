// This is a classic three-way partitioning problem, similar to the Dutch National Flag algorithm. I'll use a two-pointer approach where I maintain the invariants throughout the process.

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Partition(a: array<int>) returns (lo: int, hi: int)
  modifies a
  ensures 0 <= lo <= hi <= a.Length
  ensures forall x | 0 <= x < lo :: a[x] < 0
  ensures forall x | lo <= x < hi :: a[x] == 0
  ensures forall x | hi <= x < a.Length :: a[x] > 0
// </vc-spec>
// <vc-code>
{
  lo := 0;
  hi := a.Length;
  var i := 0;
  
  while i < hi
    invariant 0 <= lo <= i <= hi <= a.Length
    invariant forall x | 0 <= x < lo :: a[x] < 0
    invariant forall x | lo <= x < i :: a[x] == 0
    invariant forall x | hi <= x < a.Length :: a[x] > 0
  {
    if a[i] < 0 {
      // Move negative number to the front
      var temp := a[i];
      a[i] := a[lo];
      a[lo] := temp;
      lo := lo + 1;
      i := i + 1;
    } else if a[i] == 0 {
      // Zero is already in correct position
      i := i + 1;
    } else {
      // Move positive number to the back
      hi := hi - 1;
      var temp := a[i];
      a[i] := a[hi];
      a[hi] := temp;
      // Don't increment i, need to check the swapped element
    }
  }
}
// </vc-code>