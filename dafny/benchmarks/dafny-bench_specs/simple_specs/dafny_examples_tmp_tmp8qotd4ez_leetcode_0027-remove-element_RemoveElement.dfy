// SPEC
method RemoveElement(nums: array<int>, val: int) returns (newLength: int)
  modifies nums
  ensures 0 <= newLength <= nums.Length
  ensures forall x :: x in nums[..newLength] ==> x != val
  ensures multiset(nums[..newLength]) == multiset(old(nums[..]))[val := 0]
{
}
