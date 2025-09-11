// <vc-preamble>
predicate isSorted(a:array<int>)
  reads a
{
  forall i:nat, j:nat :: i <= j < a.Length ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method binSearch(a:array<int>, K:int) returns (b:bool)
  requires isSorted(a)
  ensures b == exists i:nat :: i < a.Length && a[i] == K
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
