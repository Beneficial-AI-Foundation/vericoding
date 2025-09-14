// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): No helpers needed */
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
  /* code modified by LLM (iteration 2): Fixed for loop range to handle empty arrays */
  result := new int[nums1.Length];
  for i: int := 0 to nums1.Length {
    var pos: int := 0;
    while pos < nums2.Length && nums2[pos] != nums1[i]
      decreases nums2.Length - pos
    {
      pos := pos + 1;
    }
    if pos == nums2.Length {
      result[i] := -1;
    } else {
      var j: int := pos + 1;
      while j < nums2.Length && nums2[j] <= nums1[i]
        decreases nums2.Length - j
      {
        j := j + 1;
      }
      if j < nums2.Length {
        result[i] := nums2[j];
      } else {
        result[i] := -1;
      }
    }
  }
}
// </vc-code>
