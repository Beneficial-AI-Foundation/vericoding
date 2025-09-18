// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SemiOrderedPermutation(nums: array<int>) returns (result: int)
    ensures 
        result >= 0
// </vc-spec>
// <vc-code>
{
    if nums.Length <= 1 {
        result := 0;
        return;
    }
    
    var minIndex := 0;
    var maxIndex := 0;
    
    // Find indices of minimum and maximum elements
    var i := 1;
    while i < nums.Length
        invariant 0 <= minIndex < nums.Length
        invariant 0 <= maxIndex < nums.Length
        invariant 1 <= i <= nums.Length
        invariant forall k :: 0 <= k < i ==> nums[minIndex] <= nums[k]
        invariant forall k :: 0 <= k < i ==> nums[maxIndex] >= nums[k]
    {
        if nums[i] < nums[minIndex] {
            minIndex := i;
        }
        if nums[i] > nums[maxIndex] {
            maxIndex := i;
        }
        i := i + 1;
    }
    
    // Calculate swaps needed
    var swapsForMin := minIndex;
    var swapsForMax := nums.Length - 1 - maxIndex;
    
    // Adjust if min and max would cross paths
    if minIndex > maxIndex {
        result := swapsForMin + swapsForMax - 1;
    } else {
        result := swapsForMin + swapsForMax;
    }
}
// </vc-code>
