

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method remove_element(nums: array<int>, val: int) returns (i: int)
    modifies nums
    requires 0 <= nums.Length <= 100
    requires forall i :: 0 <= i < nums.Length ==> 0 <= nums[i] <= 50
    requires 0 <= val <= 100
    ensures forall j :: 0 < j < i < nums.Length ==> nums[j] != val
// </vc-spec>
// <vc-code>
{
    i := 0;
    var writeIndex := 0;
    
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant 0 <= writeIndex <= i
        invariant forall j :: 0 <= j < writeIndex ==> nums[j] != val
    {
        if nums[i] != val {
            nums[writeIndex] := nums[i];
            writeIndex := writeIndex + 1;
        }
        i := i + 1;
    }
    
    i := writeIndex;
}
// </vc-code>

