datatype Color = Red | White | Blue

predicate Below(c: Color, d: Color)
{
    c == Red || c == d || d == Blue
}

// <vc-helpers>
// No additional helpers needed for verification
// </vc-helpers>

// <vc-spec>
method DutchFlag(a: array<Color>)
    modifies a
    ensures forall i, j :: 0 <= i < j < a.Length ==> Below(a[i], a[j])
    ensures multiset(a[..]) == multiset(old(a[..]))
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var mid := 0;
  var high := a.Length;
  while mid < high
    invariant 0 <= low <= mid <= high <= a.Length
    invariant forall i :: 0 <= i < low ==> a[i] == Red
    invariant forall i :: low <= i < mid ==> a[i] == White
    invariant forall i :: mid <= i < high ==> a[i] == Red || a[i] == White || a[i] == Blue
    invariant forall i :: high <= i < a.Length ==> a[i] == Blue
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    if a[mid] == Red {
      a[mid], a[low] := a[low], a[mid];
      low := low + 1;
      mid := mid + 1;
    } else if a[mid] == White {
      mid := mid + 1;
    } else {
      high := high - 1;
      a[mid], a[high] := a[high], a[mid];
    }
  }
}
// </vc-code>

