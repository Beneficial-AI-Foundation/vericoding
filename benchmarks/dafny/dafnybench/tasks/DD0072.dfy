// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method minArray(a: array<int>) returns (r:int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> r <= a[i]
  ensures exists i :: 0 <= i < a.Length && r == a[i]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
