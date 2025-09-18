// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
method FindNextGreater(val: int, arr: array<int>, start_index: int) returns (next_greater: int)
    requires 0 <= start_index <= arr.Length
    ensures (exists i :: start_index <= i < arr.Length && arr[i] > val) ==> next_greater > val
    ensures (forall i :: start_index <= i < arr.Length ==> arr[i] <= val) ==> next_greater == -1
{
    next_greater := -1;
    var i := start_index;
    while i < arr.Length
        invariant start_index <= i <= arr.Length
        invariant (forall k :: start_index <= k < i ==> arr[k] <= val)
        invariant next_greater == -1
    {
        if arr[i] > val {
            next_greater := arr[i];
            return;
        }
        i := i + 1;
    }
    return;
}
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
        var num1_val := nums1[i];
        var j := 0;
        while j < nums2.Length && nums2[j] != num1_val
            invariant 0 <= j <= nums2.Length
            invariant (forall k :: 0 <= k < j ==> nums2[k] != num1_val)
        {
            j := j + 1;
        }
        
        if j < nums2.Length {
            // num1_val is found at nums2[j]
            result[i] := FindNextGreater(num1_val, nums2, j + 1);
        } else {
            // This case should ideally not happen if all nums1 elements are in nums2, 
            // but we assign -1 as a fallback/default.
            // The problem statement implies nums1 is a subset of nums2, so this branch might be unreachable.
            result[i] := -1; 
        }
        i := i + 1;
    }
    return result;
}
// </vc-code>
