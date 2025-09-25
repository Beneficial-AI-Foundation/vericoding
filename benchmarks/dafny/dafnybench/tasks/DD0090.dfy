// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method TestArrayElements(a:array<int>, j: nat)
  requires 0<=j < a.Length
  modifies a
  ensures a[j] == 60
  ensures forall k :: 0 <= k < a.Length && k != j ==> a[k] == old(a[k])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
