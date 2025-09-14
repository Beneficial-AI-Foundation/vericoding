// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed helper, as the simplified implementation no longer requires it. */
// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j]
    ensures !result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] != a[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Simplified the implementation to use a single forall expression that directly reflects the postcondition. */
  result := forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j];
}
// </vc-code>
