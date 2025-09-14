

// <vc-helpers>
// No changes needed
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
  var i := 0;
  var j := 0;
  var k := a.Length;

  while j < k
    invariant 0 <= i <= j <= k <= a.Length
    invariant forall x | 0 <= x < i :: a[x] < 0
    invariant forall x | i <= x < j :: a[x] == 0
    invariant forall x | k <= x < a.Length :: a[x] > 0
    decreases k - j
  {
    if a[j] < 0 {
      a[i], a[j] := a[j], a[i]; // Swap elements
      i := i + 1;
      j := j + 1;
    } else if a[j] == 0 {
      j := j + 1;
    } else { // a[j] > 0
      k := k - 1;
      a[j], a[k] := a[k], a[j]; // Swap elements
    }
  }
  return i, j;
}
// </vc-code>

