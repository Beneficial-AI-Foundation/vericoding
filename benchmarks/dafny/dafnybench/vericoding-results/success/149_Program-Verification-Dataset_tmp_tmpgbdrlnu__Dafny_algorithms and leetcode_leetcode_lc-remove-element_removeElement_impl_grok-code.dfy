//https://leetcode.com/problems/remove-element/

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method removeElement(nums: array<int>, val: int) returns (i: int)
    ensures forall k :: 0 < k < i < nums.Length ==> nums[k] != val
    modifies nums
// </vc-spec>
// <vc-code>
{
  var idx := 0;
  var j := 0;
  while j < nums.Length
    invariant 0 <= idx <= nums.Length
    invariant 0 <= j <= nums.Length
    invariant forall k :: 0 < k < idx ==> nums[k] != val
    invariant idx <= j
  {
    if nums[j] != val {
      nums[idx] := nums[j];
      idx := idx + 1;
    }
    j := j + 1;
  }
  return idx;
}
// </vc-code>

///compileTarget:js