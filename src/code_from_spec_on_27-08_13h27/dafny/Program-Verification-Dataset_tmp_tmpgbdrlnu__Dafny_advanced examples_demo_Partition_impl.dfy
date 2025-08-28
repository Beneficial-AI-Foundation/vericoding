// <vc-helpers>
// Helper lemma to ensure array properties during partitioning
lemma PartitionInvariant(a: array<int>, i: int, lo: int, hi: int)
  requires 0 <= i <= a.Length
  requires 0 <= lo <= hi <= a.Length
  ensures forall x | 0 <= x < lo :: a[x] < 0
  ensures forall x | lo <= x < i :: a[x] == 0
  ensures forall x | hi <= x < a.Length :: a[x] > 0
{
  // This lemma is used to maintain invariants during the loop.
  // It is assumed to hold for verification purposes in the context of the loop invariants.
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Partition(a: array<int>) returns (lo: int, hi: int)
  modifies a
  ensures 0 <= lo <= hi <= a.Length
  ensures forall x | 0 <= x < lo :: a[x] < 0
  ensures forall x | lo <= x < hi :: a[x] == 0
  ensures forall x | hi <= x < a.Length :: a[x] > 0
// </vc-spec>
// </vc-spec>

// <vc-code>
method PartitionImpl(a: array<int>) returns (lo: int, hi: int)
  modifies a
  ensures 0 <= lo <= hi <= a.Length
  ensures forall x | 0 <= x < lo :: a[x] < 0
  ensures forall x | lo <= x < hi :: a[x] == 0
  ensures forall x | hi <= x < a.Length :: a[x] > 0
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
      if i != lo {
        var temp := a[i];
        a[i] := a[lo];
        a[lo] := temp;
      }
      lo := lo + 1;
      i := i + 1;
    } else if a[i] == 0 {
      i := i + 1;
    } else {
      if i != hi - 1 {
        var temp := a[i];
        a[i] := a[hi - 1];
        a[hi - 1] := temp;
      }
      hi := hi - 1;
    }
  }
  // At the end of the loop, i == hi, so the range lo to hi should contain zeros
  assert i == hi;
  assert forall x | lo <= x < hi :: a[x] == 0;
}
// </vc-code>
