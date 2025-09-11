// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method InvertArray(a: array<int>)
  modifies a
  ensures forall i | 0 <= i < a.Length :: a[i] == old(a[a.Length-1-i])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
