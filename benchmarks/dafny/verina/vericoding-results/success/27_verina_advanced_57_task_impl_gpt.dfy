// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): retain simple min helper for completeness */
function min(a: int, b: int): int { if a < b then a else b }
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
  /* code modified by LLM (iteration 2): removed null-check invariant; implemented next greater search */
  result := new int[nums1.Length];
  var i := 0;
  while i < nums1.Length
    invariant 0 <= i <= nums1.Length
    invariant result.Length == nums1.Length
  {
    var target := nums1[i];
    var j := 0;
    var idx := -1;
    while j < nums2.Length
      invariant 0 <= j <= nums2.Length
      invariant -1 <= idx < nums2.Length
    {
      if idx == -1 && nums2[j] == target {
        idx := j;
      }
      j := j + 1;
    }
    var answer := -1;
    if idx != -1 {
      var k := idx + 1;
      while k < nums2.Length
        invariant idx + 1 <= k <= nums2.Length
      {
        if nums2[k] > target {
          answer := nums2[k];
          k := nums2.Length;
        } else {
          k := k + 1;
        }
      }
    }
    result[i] := answer;
    i := i + 1;
  }
}
// </vc-code>
