// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed redundant null check and defined monotonicity over array contents */
predicate IsNondecreasing(arr: array<int>) reads arr { forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j] }
// </vc-helpers>

// <vc-spec>
method IsSorted(arr: array<int>) returns (is_sorted: bool)

    requires
        arr.Length > 0

    ensures
        is_sorted == (forall i, j :: 0 <= i < j < arr.Length ==> (arr[i] <= arr[j]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): compute sortedness with a quantifier matching the specification */
  is_sorted := forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j];
}
// </vc-code>
