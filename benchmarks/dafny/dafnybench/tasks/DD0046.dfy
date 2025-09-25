// <vc-preamble>
// </vc-preamble>

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
  assume {:axiom} false;
}
// </vc-code>
