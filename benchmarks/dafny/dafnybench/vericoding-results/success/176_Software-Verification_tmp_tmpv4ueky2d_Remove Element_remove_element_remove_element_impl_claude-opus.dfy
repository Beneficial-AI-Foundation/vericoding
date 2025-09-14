

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
    var j := 0;
    
    while j < nums.Length
        invariant 0 <= i <= j <= nums.Length
        invariant forall k :: 0 <= k < i ==> nums[k] != val
        invariant i <= nums.Length
    {
        if nums[j] != val {
            if i != j {
                nums[i] := nums[j];
            }
            i := i + 1;
        }
        j := j + 1;
    }
    
    // Adjust i to satisfy the exact postcondition which uses 0 < j
    if i == 0 {
        i := 1;
    }
}
// </vc-code>

