// SPEC
//https://leetcode.com/problems/remove-element/
method removeElement(nums: array<int>, val: int) returns (i: int)
  ensures forall k :: 0 < k < i < nums.Length ==> nums[k] != val
  modifies nums
{
}
