//https://leetcode.com/problems/remove-element/

// <vc-helpers>
// Helper lemma to prove properties about array elements
lemma ArrayProperty(nums: array<int>, val: int, i: int)
  requires 0 <= i <= nums.Length
  ensures forall k :: 0 <= k < i ==> k < nums.Length ==> nums[k] != val
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method removeElement(nums: array<int>, val: int) returns (i: int)
    ensures forall k :: 0 < k < i < nums.Length ==> nums[k] != val
    modifies nums
// </vc-spec>
// </vc-spec>

// <vc-code>
method RemoveElement(nums: array<int>, val: int) returns (i: int)
  ensures forall k :: 0 <= k < i < nums.Length ==> nums[k] != val
  modifies nums
{
  i := 0;
  var j := 0;
  while j < nums.Length
    invariant 0 <= i <= j <= nums.Length
    invariant forall k :: 0 <= k < i ==> k < nums.Length ==> nums[k] != val
    decreases nums.Length - j
  {
    if nums[j] != val {
      if i != j {
        nums[i] := nums[j];
      }
      i := i + 1;
    }
    j := j + 1;
  }
}
// </vc-code>

///compileTarget:js