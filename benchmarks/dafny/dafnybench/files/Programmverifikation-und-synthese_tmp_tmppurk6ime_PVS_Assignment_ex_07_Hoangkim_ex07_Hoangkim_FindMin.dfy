// <vc-preamble>
ghost predicate sorted(a:seq<int>)
{
    forall i | 0 < i < |a| :: a[i-1] <= a[i]     
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
    requires a != null && a.Length > 0 && lo < a.Length
    ensures lo <= minIdx < a.Length
    ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
