

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method arrayProduct(a: array<int>, b: array<int>) returns (c: array<int> )
  requires a.Length==b.Length
  ensures c.Length==a.Length
  ensures forall i:: 0 <= i< a.Length==> a[i] * b[i]==c[i]
// </vc-spec>
// <vc-code>
{
  c := new int[a.Length];
  var index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant forall i :: 0 <= i < index ==> a[i] * b[i] == c[i]
    invariant c.Length == a.Length
  {
    c[index] := a[index] * b[index];
    index := index + 1;
  }
}
// </vc-code>

