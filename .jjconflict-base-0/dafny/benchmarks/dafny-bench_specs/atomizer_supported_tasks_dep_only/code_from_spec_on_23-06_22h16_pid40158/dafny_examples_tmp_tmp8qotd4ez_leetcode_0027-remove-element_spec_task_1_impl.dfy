//IMPL 
method RemoveElement(nums: array<int>, val: int) returns (newLength: int)
    modifies nums
    ensures 0 <= newLength <= nums.Length
    ensures forall x :: x in nums[..newLength] ==> x != val
    ensures multiset(nums[..newLength]) == multiset(old(nums[..]))[val := 0]
{
    newLength := 0;
    var i := 0;
    
    /* code modified by LLM (iteration 4): Fixed invariants to properly track multiset relationship - the result contains exactly the non-val elements from processed portion, and unprocessed portion is unchanged */
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant 0 <= newLength <= i
        invariant forall x :: x in nums[..newLength] ==> x != val
        invariant multiset(nums[..newLength]) == multiset(old(nums[..i])) - multiset{val} * (i - newLength)
        invariant nums[i..] == old(nums[i..])
    {
        if nums[i] != val {
            nums[newLength] := nums[i];
            newLength := newLength + 1;
        }
        i := i + 1;
    }
}