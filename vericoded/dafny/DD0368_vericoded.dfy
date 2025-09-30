

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
      a[i], a[lo] := a[lo], a[i];
      lo := lo + 1;
      i := i + 1;
    } else if a[i] == 0 {
      i := i + 1;
    } else {
      hi := hi - 1;
      a[i], a[hi] := a[hi], a[i];
    }
  }
}
// </vc-code>

