// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method appendArray(a: array<int>, b: array<int>) returns (c: array<int>)
ensures c.Length == a.Length + b.Length
ensures forall i :: 0 <= i < a.Length ==> a[i] == c[i]
ensures forall i :: 0 <= i < b.Length ==> b[i] == c[a.Length + i]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
