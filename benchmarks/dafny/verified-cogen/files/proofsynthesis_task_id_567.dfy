// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
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
    assume {:axiom} false;
}
// </vc-code>
