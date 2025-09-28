// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function indexOfK(k: int): int { k - 1 }
// </vc-helpers>

// <vc-spec>
method KthElementImpl(arr: array<int>, k: int) returns (result: int)
    requires k >= 1 && k <= arr.Length
    ensures result == arr[k - 1]
// </vc-spec>
// <vc-code>
{
  result := arr[k - 1];
}
// </vc-code>
