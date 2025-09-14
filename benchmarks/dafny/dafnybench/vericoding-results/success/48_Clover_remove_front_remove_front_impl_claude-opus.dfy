

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method remove_front(a:array<int>) returns (c:array<int>)
  requires a.Length>0
  ensures  a[1..] == c[..]
// </vc-spec>
// <vc-code>
{
  c := new int[a.Length - 1];
  var i := 0;
  while i < c.Length
    invariant 0 <= i <= c.Length
    invariant forall j :: 0 <= j < i ==> c[j] == a[j + 1]
  {
    c[i] := a[i + 1];
    i := i + 1;
  }
}
// </vc-code>

