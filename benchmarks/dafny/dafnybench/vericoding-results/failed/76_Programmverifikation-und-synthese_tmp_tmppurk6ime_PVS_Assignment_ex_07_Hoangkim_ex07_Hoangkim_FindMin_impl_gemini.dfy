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
  /* code modified by LLM (iteration 5): Corrected the for-loop syntax from 'to' to '..', which is idiomatic Dafny and resolves the verifier's bound error. */
  minIdx := lo;
  for i := lo + 1 .. a.Length
    invariant lo <= minIdx < a.Length
    invariant forall k :: lo <= k < i ==> a[minIdx] <= a[k]
  {
    if a[i] < a[minIdx] {
      minIdx := i;
    }
  }
}
// </vc-code>
