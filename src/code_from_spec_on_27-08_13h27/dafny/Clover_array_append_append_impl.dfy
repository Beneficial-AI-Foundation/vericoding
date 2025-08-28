// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method append(a:array<int>, b:int) returns (c:array<int>)
  ensures  a[..] + [b] == c[..]
// </vc-spec>
// </vc-spec>

// <vc-code>
method Append(a: array<int>, b: int) returns (c: array<int>)
  ensures c[..] == a[..] + [b]
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
}
// </vc-code>
