// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Max(x: int, y: int): int { if x >= y then x else y }
// </vc-helpers>

// <vc-spec>
method NextGreaterElement(nums1: array<int>, nums2: array<int>) returns (result: array<int>)
    requires
        forall i, j :: 0 <= i < nums1.Length && 0 <= j < nums1.Length && i != j ==> nums1[i] != nums1[j]
    requires
        forall i, j :: 0 <= i < nums2.Length && 0 <= j < nums2.Length && i != j ==> nums2[i] != nums2[j]
    ensures
        result.Length == nums1.Length
// </vc-spec>
// <vc-code>
{
  result := new int[nums1.Length];
}
// </vc-code>
