// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed, helper is correct. */
predicate IsUniqueUpto(a: array<int>, k: int)
  reads a
  requires 0 <= k <= a.Length
{
  forall j :: 1 <= j < k ==> a[j-1] != a[j]
}
// </vc-helpers>

// <vc-spec>
method NoDups (a : array<int>) returns (noDups : bool)
    requires forall j : int :: 0 < j < a.Length ==> a[j-1] <= a[j]
    ensures noDups <==> forall j : int :: 1 <= j < a.Length ==> a[j-1] != a[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Guarded the loop with 'if a.Length > 0' to ensure the loop invariant holds on entry, which previously failed for zero-length arrays. */
  noDups := true;
  if a.Length > 0 {
    var i := 1;
    while i < a.Length
      invariant 1 <= i <= a.Length
      invariant noDups <==> IsUniqueUpto(a, i)
    {
      if a[i-1] == a[i] {
        noDups := false;
        return;
      }
      i := i + 1;
    }
  }
}
// </vc-code>
