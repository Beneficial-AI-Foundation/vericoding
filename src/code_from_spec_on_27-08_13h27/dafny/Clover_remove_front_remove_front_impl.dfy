// <vc-helpers>
// No additional helper code or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method remove_front(a:array<int>) returns (c:array<int>)
  requires a.Length>0
  ensures  a[1..] == c[..]
// </vc-spec>
// </vc-spec>

// <vc-code>
method RemoveFront(a: array<int>) returns (c: array<int>)
  requires a.Length > 0
  ensures a[1..] == c[..]
{
  c := new int[a.Length - 1];
  var i := 0;
  while i < a.Length - 1
    invariant 0 <= i <= a.Length - 1
    invariant forall k :: 0 <= k < i ==> c[k] == a[k + 1]
  {
    c[i] := a[i + 1];
    i := i + 1;
  }
}
// </vc-code>
