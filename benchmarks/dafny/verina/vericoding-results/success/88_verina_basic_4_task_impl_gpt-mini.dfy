// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma KthIndexInRange(arr: array<int>, k: int)
    requires k >= 1 && k <= arr.Length
    ensures 0 <= k - 1 < arr.Length
{
}

// </vc-helpers>

// <vc-spec>
method KthElementImpl(arr: array<int>, k: int) returns (result: int)
    requires k >= 1 && k <= arr.Length
    ensures result == arr[k - 1]
// </vc-spec>
// <vc-code>
{
    // impl-start
    result := arr[k - 1];
    // impl-end
}

// </vc-code>
