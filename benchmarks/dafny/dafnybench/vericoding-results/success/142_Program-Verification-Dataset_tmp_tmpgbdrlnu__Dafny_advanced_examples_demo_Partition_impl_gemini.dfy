// <vc-preamble>
// </vc-preamble>

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
  var mid := 0;

  while mid < hi
    invariant 0 <= lo <= mid <= hi <= a.Length
    invariant forall i | 0 <= i < lo :: a[i] < 0
    invariant forall i | lo <= i < mid :: a[i] == 0
    invariant forall i | hi <= i < a.Length :: a[i] > 0
  {
    if a[mid] < 0 {
      a[lo], a[mid] := a[mid], a[lo];
      lo := lo + 1;
      mid := mid + 1;
    } else if a[mid] == 0 {
      mid := mid + 1;
    } else {
      hi := hi - 1;
      a[mid], a[hi] := a[hi], a[mid];
    }
  }
}
// </vc-code>
