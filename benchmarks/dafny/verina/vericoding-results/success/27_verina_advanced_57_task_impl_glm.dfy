// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): changed to methods to allow loops */
method FindNextGreater(nums: array<int>, index: int) returns (res: int)
    requires 0 <= index < nums.Length
    ensures res == -1 || res > nums[index]
{
    var i := index + 1;
    while i < nums.Length
        invariant index < i <= nums.Length
    {
        if nums[i] > nums[index] {
            res := nums[i];
            return;
        }
        i := i + 1;
    }
    res := -1;
}

/* helper modified by LLM (iteration 2): changed to method to allow loops */
method FindIndex(nums: array<int>, value: int) returns (res: int)
    requires forall i, j :: 0 <= i < nums.Length && 0 <= j < nums.Length && i != j ==> nums[i] != nums[j]
    ensures 0 <= res < nums.Length || res == -1
    ensures res == -1 ==> forall i :: 0 <= i < nums.Length ==> nums[i] != value
    ensures res != -1 ==> nums[res] == value
{
    var i := 0;
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant forall j :: 0 <= j < i ==> nums[j] != value
    {
        if nums[i] == value {
            res := i;
            return;
        }
        i := i + 1;
    }
    res := -1;
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
    /* code modified by LLM (iteration 2): using helper methods */
    result := new int[nums1.Length];
    var i := 0;
    while i < nums1.Length
        invariant 0 <= i <= nums1.Length
    {
        var idx := FindIndex(nums2, nums1[i]);
        if idx != -1 {
            result[i] := FindNextGreater(nums2, idx);
        } else {
            result[i] := -1;
        }
        i := i + 1;
    }
}
// </vc-code>
