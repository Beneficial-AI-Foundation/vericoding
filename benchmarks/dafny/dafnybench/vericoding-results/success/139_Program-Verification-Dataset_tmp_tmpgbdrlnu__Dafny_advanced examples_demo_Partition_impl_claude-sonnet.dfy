

// <vc-helpers>
lemma MultisetPreservation(a: array<int>, old_a: seq<int>)
  requires a.Length == |old_a|
  ensures multiset(a[..]) == multiset(old_a) ==> multiset(a[..]) == multiset(old_a)
{
}
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
  hi := 0;
  
  while hi < a.Length
    invariant 0 <= lo <= hi <= a.Length
    invariant forall x | 0 <= x < lo :: a[x] < 0
    invariant forall x | lo <= x < hi :: a[x] == 0
    invariant multiset(a[..]) == old(multiset(a[..]))
    decreases a.Length - hi
  {
    if a[hi] < 0 {
      a[lo], a[hi] := a[hi], a[lo];
      lo := lo + 1;
      hi := hi + 1;
    } else if a[hi] == 0 {
      hi := hi + 1;
    } else {
      var end := a.Length - 1;
      while end > hi && a[end] > 0
        invariant hi <= end < a.Length
        invariant forall x | end < x < a.Length :: a[x] > 0
        invariant forall x | 0 <= x < lo :: a[x] < 0
        invariant forall x | lo <= x < hi :: a[x] == 0
        invariant multiset(a[..]) == old(multiset(a[..]))
        decreases end - hi
      {
        end := end - 1;
      }
      if end > hi {
        a[hi], a[end] := a[end], a[hi];
        if a[hi] < 0 {
          a[lo], a[hi] := a[hi], a[lo];
          lo := lo + 1;
        }
        hi := hi + 1;
      } else {
        break;
      }
    }
  }
}
// </vc-code>

