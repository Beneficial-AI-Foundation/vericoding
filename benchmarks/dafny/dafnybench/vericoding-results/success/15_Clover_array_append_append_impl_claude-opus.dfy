

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method append(a:array<int>, b:int) returns (c:array<int>)
  ensures  a[..] + [b] == c[..]
// </vc-spec>
// <vc-code>
{
  c := new int[a.Length + 1];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> c[j] == a[j]
  {
    c[i] := a[i];
    i := i + 1;
  }
  c[a.Length] := b;
  assert c[..a.Length] == a[..];
  assert c[a.Length] == b;
  assert c[..] == c[..a.Length] + [c[a.Length]];
  assert c[..] == a[..] + [b];
}
// </vc-code>

