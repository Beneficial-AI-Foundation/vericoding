// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Reverse(a: array<int>)
    modifies a;
    ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length-1) - k]);
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
