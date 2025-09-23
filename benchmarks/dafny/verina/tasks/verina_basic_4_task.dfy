// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
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
