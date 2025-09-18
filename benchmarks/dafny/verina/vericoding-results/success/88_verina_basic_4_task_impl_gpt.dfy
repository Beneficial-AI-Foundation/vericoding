// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate ValidK(k: int, n: int) { 1 <= k <= n }
function Index0(k: int): int { k - 1 }
lemma OneBasedToZeroBasedBound(k: int, n: int)
  requires ValidK(k, n)
  ensures 0 <= Index0(k) < n
{ }
// </vc-helpers>

// <vc-spec>
method KthElementImpl(arr: array<int>, k: int) returns (result: int)
    requires k >= 1 && k <= arr.Length
    ensures result == arr[k - 1]
// </vc-spec>
// <vc-code>
{
  // impl-start
  // Establish bounds from 1-based k
  OneBasedToZeroBasedBound(k, arr.Length);
  result := arr[Index0(k)];
  // impl-end
}
// </vc-code>
