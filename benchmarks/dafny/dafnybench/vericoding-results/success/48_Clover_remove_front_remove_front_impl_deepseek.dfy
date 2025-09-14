

// <vc-helpers>
lemma ArraySliceEqualsLemma<T>(a: array<T>, b: array<T>, start: int)
  requires 0 <= start <= a.Length
  requires b.Length == a.Length - start
  requires forall i | 0 <= i < b.Length :: b[i] == a[start + i]
  ensures a[start..] == b[..]
{
}
// </vc-helpers>

// <vc-spec>
method remove_front(a:array<int>) returns (c:array<int>)
  requires a.Length>0
  ensures  a[1..] == c[..]
// </vc-spec>
// <vc-code>
{
  var len := a.Length - 1;
  c := new int[len];
  var i := 0;
  while i < len
    invariant 0 <= i <= len
    invariant forall j | 0 <= j < i :: c[j] == a[j + 1]
  {
    c[i] := a[i + 1];
    i := i + 1;
  }
  ArraySliceEqualsLemma(a, c, 1);
}
// </vc-code>

