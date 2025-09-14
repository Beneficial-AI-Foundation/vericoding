

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method remove_front(a:array<int>) returns (c:array<int>)
  requires a.Length>0
  ensures  a[1..] == c[..]
// </vc-spec>
// <vc-code>
{
  var n := a.Length - 1;
  c := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant c.Length == n
    invariant forall k :: 0 <= k < i ==> c[k] == a[k + 1]
  {
    c[i] := a[i + 1];
    i := i + 1;
  }
  assert c.Length == a.Length - 1;
  assert forall k :: 0 <= k < c.Length ==> c[k] == a[k + 1];
  assert c[..] == a[1..];
}
// </vc-code>

