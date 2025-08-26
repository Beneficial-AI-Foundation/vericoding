method RemoveElement(nums: array<int>, val: int) returns (newLength: int)
    modifies nums
    ensures 0 <= newLength <= nums.Length
    ensures forall x :: x in nums[..newLength] ==> x != val
    ensures multiset(nums[..newLength]) == multiset(old(nums[..]))[val := 0]
</vc-spec>
<vc-code>
{
    var writeIndex := 0;
    var i := 0;
    
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant 0 <= writeIndex <= i
        invariant forall x :: x in nums[..writeIndex] ==> x != val
        invariant multiset(nums[..writeIndex]) + multiset(nums[i..]) == multiset(old(nums[..]))[val := 0]
    {
        if nums[i] != val {
            nums[writeIndex] := nums[i];
            writeIndex := writeIndex + 1;
        }
        i := i + 1;
    }
    
    newLength := writeIndex;
}
</vc-code>

<vc-helpers>
</vc-helpers>