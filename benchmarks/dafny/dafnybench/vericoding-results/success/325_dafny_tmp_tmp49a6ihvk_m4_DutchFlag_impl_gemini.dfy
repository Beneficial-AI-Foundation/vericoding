// <vc-preamble>
datatype Color = Red | White | Blue

predicate Below(c: Color, d: Color)
{
    c == Red || c == d || d == Blue
}
// </vc-preamble>

// <vc-helpers>
predicate IsPartitioned(a: seq<Color>, r: int, w: int, b: int)
{
  0 <= r <= w <= b <= |a| &&
  (forall i :: 0 <= i < r ==> a[i] == Red) &&
  (forall i :: r <= i < w ==> a[i] == White) &&
  (forall i :: b <= i < |a| ==> a[i] == Blue)
}
// </vc-helpers>

// <vc-spec>
method DutchFlag(a: array<Color>)
    modifies a
    ensures forall i, j :: 0 <= i < j < a.Length ==> Below(a[i], a[j])
    ensures multiset(a[..]) == multiset(old(a[..]))
// </vc-spec>
// <vc-code>
{
  var r := 0;
  var w := 0;
  var b := a.Length;

  while w < b
    invariant IsPartitioned(a[..], r, w, b)
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases b - w
  {
    if a[w] == Red {
      a[r], a[w] := a[w], a[r];
      r := r + 1;
      w := w + 1;
    } else if a[w] == White {
      w := w + 1;
    } else { // a[w] is Blue
      b := b - 1;
      a[b], a[w] := a[w], a[b];
    }
  }
}
// </vc-code>
