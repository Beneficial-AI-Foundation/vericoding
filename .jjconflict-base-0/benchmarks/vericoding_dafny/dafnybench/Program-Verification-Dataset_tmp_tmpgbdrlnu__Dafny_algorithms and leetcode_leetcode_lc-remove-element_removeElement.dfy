//https://leetcode.com/problems/remove-element/

// <vc-helpers>
// </vc-helpers>

method removeElement(nums: array<int>, val: int) returns (i: int)
    ensures forall k :: 0 < k < i < nums.Length ==> nums[k] != val
    modifies nums
// <vc-code>
{
  assume false;
}
// </vc-code>

///compileTarget:js