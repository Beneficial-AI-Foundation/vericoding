

// <vc-helpers>
// No helpers needed
// </vc-helpers>

// <vc-spec>
method ArraySplit (a : array<int>) returns (b : array<int>, c : array<int>)
  ensures fresh(b)
  ensures fresh(c)
  ensures a[..] == b[..] + c[..]
  ensures a.Length == b.Length + c.Length
  ensures a.Length > 1 ==> a.Length > b.Length
  ensures a.Length > 1 ==> a.Length > c.Length
// </vc-spec>
// <vc-code>
{
  var bLen := a.Length / 2;
  b := new int[bLen];
  c := new int[a.Length - bLen];
  var i := 0;
  while i < bLen
    invariant 0 <= i <= bLen
    invariant forall k :: 0 <= k < i ==> b[k] == a[k]
  {
    b[i] := a[i];
    i := i + 1;
  }
  i := 0;
  while i < c.Length
    invariant 0 <= i <= c.Length
    invariant forall k :: 0 <= k < b.Length ==> b[k] == a[k]
    invariant forall k :: 0 <= k < i ==> c[k] == a[b.Length + k]
  {
    c[i] := a[b.Length + i];
    i := i + 1;
  }
}
// </vc-code>

