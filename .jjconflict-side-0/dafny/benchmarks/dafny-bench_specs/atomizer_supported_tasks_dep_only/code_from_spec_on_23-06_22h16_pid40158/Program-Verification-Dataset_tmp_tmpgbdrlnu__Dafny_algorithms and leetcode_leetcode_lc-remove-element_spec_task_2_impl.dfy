//IMPL removeElement
//https://leetcode.com/problems/remove-element/
method removeElement(nums: array<int>, val: int) returns (i: int)
    ensures forall k :: 0 < k < i < nums.Length ==> nums[k] != val
    modifies nums
{
    i := 0;
    var j := 0;
    
    while j < nums.Length
        invariant 0 <= i <= j <= nums.Length
        invariant forall k :: 0 <= k < i ==> nums[k] != val
    {
        if nums[j] != val {
            nums[i] := nums[j];
            i := i + 1;
        }
        j := j + 1;
    }
}

//IMPL Main
///compileTarget:js
method Main() {
}