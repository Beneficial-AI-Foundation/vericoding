

// <vc-helpers>
lemma RealSubtractionLemma(a: real, b: real, c: real)
  ensures a - b == c <==> a == b + c
{
}
// </vc-helpers>

// <vc-spec>
method ParabolaDirectrix(a: real, h: real, k: real) returns (directrix: real)
    requires a != 0.0
    ensures directrix == k - 1.0 / (4.0 * a)
// </vc-spec>
// <vc-code>
{
  directrix := k - 1.0 / (4.0 * a);
}
// </vc-code>

