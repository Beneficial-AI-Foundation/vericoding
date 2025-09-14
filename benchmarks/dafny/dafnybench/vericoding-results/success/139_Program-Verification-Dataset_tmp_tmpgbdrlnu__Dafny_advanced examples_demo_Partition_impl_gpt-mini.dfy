

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
  var l := 0;
  var m := 0;
  var h_local := a.Length;
  while m < h_local
    invariant 0 <= l <= m <= h_local <= a.Length
    invariant forall k | 0 <= k < l :: a[k] < 0
    invariant forall k | l <= k < m :: a[k] == 0
    invariant forall k | h_local <= k < a.Length :: a[k] > 0
    decreases h_local - m
  {
    if a[m] < 0 {
      var tmp := a[l];
      a[l] := a[m];
      a[m] := tmp;
      l := l + 1;
      m := m + 1;
    } else if a[m] == 0 {
      m := m + 1;
    } else {
      var tmp := a[m];
      a[m] := a[h_local - 1];
      a[h_local - 1] := tmp;
      h_local := h_local - 1;
    }
  }
  lo := l;
  hi := h_local;
}
// </vc-code>

