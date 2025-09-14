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
    var i := 0;
    while i < arr.Length - 1
        invariant 0 <= i < arr.Length
        invariant forall k, l :: 0 <= k < l <= i ==> arr[k] <= arr[l]
    {
        if arr[i] > arr[i+1] {
            return false;
        }
        i := i + 1;
    }
    return true;
}
// </vc-code>
