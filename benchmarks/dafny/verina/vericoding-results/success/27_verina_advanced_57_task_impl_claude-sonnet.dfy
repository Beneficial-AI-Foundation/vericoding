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
    
    for i := 0 to nums1.Length
        invariant 0 <= i <= nums1.Length
        invariant result.Length == nums1.Length
    {
        var num := nums1[i];
        var found := false;
        var nextGreater := -1;
        
        // Find num in nums2
        var j := 0;
        while j < nums2.Length && nums2[j] != num
            invariant 0 <= j <= nums2.Length
        {
            j := j + 1;
        }
        
        // If found, look for next greater element
        if j < nums2.Length {
            var k := j + 1;
            while k < nums2.Length && !found
                invariant j < k <= nums2.Length
                invariant !found ==> forall l :: j < l < k ==> nums2[l] <= num
            {
                if nums2[k] > num {
                    nextGreater := nums2[k];
                    found := true;
                }
                k := k + 1;
            }
        }
        
        result[i] := nextGreater;
    }
}
// </vc-code>
