// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method arrayProduct(a: array<int>, b: array<int>) returns (c: array<int> )
  requires a.Length==b.Length
  ensures c.Length==a.Length
  ensures forall i:: 0 <= i< a.Length==> a[i] * b[i]==c[i]
// </vc-spec>
// </vc-spec>

// <vc-code>
method ArrayProduct(a: array<int>, b: array<int>) returns (c: array<int>)
  requires a.Length == b.Length
  ensures c.Length == a.Length
  ensures forall i :: 0 <= i < a.Length ==> c[i] == a[i] * b[i]
{
  c := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> c[k] == a[k] * b[k]
  {
    c[i] := a[i] * b[i];
    i := i + 1;
  }
}
// </vc-code>
