// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma SortedArrayGreater(arr: array<int>, i: int, target: int)
    requires forall k, j :: 0 <= k < j < arr.Length ==> arr[k] <= arr[j]
    requires 0 <= i < arr.Length
    requires arr[i] > target
    ensures forall j :: i <= j < arr.Length ==> arr[j] > target
{
    /* helper modified by LLM (iteration 2): fixed lemma body to prove arr[j] > target */
    forall j | i <= j < arr.Length
        ensures arr[j] > target
    {
        assert arr[i] <= arr[j];
        assert arr[i] > target;
        assert arr[j] >= arr[i] > target;
    }
}
// </vc-helpers>

// <vc-spec>
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)

    requires
        forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]

    ensures
        if index >= 0 then (
            && 0 <= index < arr.Length
            && (forall k :: 0 <= k < index ==> arr[k] != target)
            && arr[index] == target
        ) else (
            forall k :: 0 <= k < arr.Length ==> arr[k] != target
        )
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): removed 'then' keyword in if statement to fix parse error */
    index := -1;
    var i := 0;
    while i < arr.Length && arr[i] <= target
        invariant 0 <= i <= arr.Length
        invariant forall k :: 0 <= k < i ==> arr[k] != target
    {
        if arr[i] == target {
            index := i;
            break;
        }
        i := i + 1;
    }
    if index == -1 && i < arr.Length {
        SortedArrayGreater(arr, i, target);
    }
}
// </vc-code>
