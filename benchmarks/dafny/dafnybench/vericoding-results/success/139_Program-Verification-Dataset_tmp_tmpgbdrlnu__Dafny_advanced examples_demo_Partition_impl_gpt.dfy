

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
  var n := a.Length;
  var i := 0;
  var j := 0;
  var k := n;
  while j < k
    invariant 0 <= i <= j <= k <= a.Length
    invariant forall x | 0 <= x < i :: a[x] < 0
    invariant forall x | i <= x < j :: a[x] == 0
    invariant forall x | k <= x < a.Length :: a[x] > 0
    decreases k - j
  {
    if a[j] < 0 {
      var tmp := a[i];
      a[i] := a[j];
      a[j] := tmp;
      i := i + 1;
      j := j + 1;
    } else if a[j] == 0 {
      j := j + 1;
    } else {
      k := k - 1;
      var tmp2 := a[j];
      a[j] := a[k];
      a[k] := tmp2;
    }
  }
  lo := i;
  hi := j;
}
// </vc-code>

