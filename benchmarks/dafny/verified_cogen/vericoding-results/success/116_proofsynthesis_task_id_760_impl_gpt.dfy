// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed redundant null-check to avoid warning */
predicate AllEqualToFirst(a: array<int>) reads a {
  forall i :: 1 <= i < a.Length ==> a[0] == a[i]
}
// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(arr: array<int>) returns (result: bool)
    ensures result == (forall i :: 1 <= i < arr.Length ==> arr[0] == arr[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): compute result directly from the specification */
  result := (forall i :: 1 <= i < arr.Length ==> arr[0] == arr[i]);
}
// </vc-code>
