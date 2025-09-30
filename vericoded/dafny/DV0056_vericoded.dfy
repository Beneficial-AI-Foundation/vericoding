// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  var i := 0;
  while i < nums1.Length
    invariant 0 <= i <= nums1.Length
    invariant result.Length == nums1.Length
  {
    var idx := -1;
    var j := 0;
    while j < nums2.Length
      invariant 0 <= j <= nums2.Length
    {
      if nums2[j] == nums1[i] {
        idx := j;
        break;
      }
      j := j + 1;
    }
    
    if idx == -1 {
      result[i] := -1;
    } else {
      var nextGreater := -1;
      var k := idx + 1;
      while k < nums2.Length
        invariant idx < k <= nums2.Length
      {
        if nums2[k] > nums2[idx] {
          nextGreater := nums2[k];
          break;
        }
        k := k + 1;
      }
      result[i] := nextGreater;
    }
    i := i + 1;
  }
}
// </vc-code>
