// <vc-preamble>
// </vc-preamble>

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
    invariant c.Length == a.Length - 1
    invariant forall k :: 0 <= k < i ==> c[k] == a[k+1]
  {
    c[i] := a[i+1];
    i := i + 1;
  }
}
// </vc-code>
