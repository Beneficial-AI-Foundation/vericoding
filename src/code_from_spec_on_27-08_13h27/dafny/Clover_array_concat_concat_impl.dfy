// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method concat(a:array<int>, b:array<int>) returns (c:array<int>)
  ensures c.Length==b.Length+a.Length
  ensures forall k :: 0 <= k < a.Length ==> c[k] == a[k]
  ensures forall k :: 0 <= k < b.Length ==> c[k+a.Length] == b[k]
// </vc-spec>
// </vc-spec>

// <vc-code>
method Concatenate(a: array<int>, b: array<int>) returns (c: array<int>)
  ensures c.Length == a.Length + b.Length
  ensures forall k :: 0 <= k < a.Length ==> c[k] == a[k]
  ensures forall k :: 0 <= k < b.Length ==> c[k + a.Length] == b[k]
{
  c := new int[a.Length + b.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> c[k] == a[k]
  {
    c[i] := a[i];
    i := i + 1;
  }
  i := 0;
  while i < b.Length
    invariant 0 <= i <= b.Length
    invariant forall k :: 0 <= k < a.Length ==> c[k] == a[k]
    invariant forall k :: 0 <= k < i ==> c[k + a.Length] == b[k]
  {
    c[i + a.Length] := b[i];
    i := i + 1;
  }
}
// </vc-code>
