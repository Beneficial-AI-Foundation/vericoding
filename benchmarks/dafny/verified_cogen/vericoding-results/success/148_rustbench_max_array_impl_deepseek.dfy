// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma MaxIndexLemma(nums: seq<int>, idx1: int, idx2: int)
  requires 0 <= idx1 < |nums|
  requires 0 <= idx2 < |nums|
  ensures nums[idx1] <= nums[idx2] || nums[idx2] <= nums[idx1]
{
  // The comparison property holds by integer ordering
}
// </vc-helpers>

// <vc-spec>
method MaxArray(nums: array<int>) returns (idx: int)
    requires
        nums.Length >= 1
    ensures
        0 <= idx && idx < nums.Length &&
        forall i :: 0 <= i && i < nums.Length ==> nums[i] <= nums[idx]
// </vc-spec>
// <vc-code>
{
  idx := 0;
  var currentMax := nums[0];
  
  var index := 1;
  while index < nums.Length
    invariant 0 <= idx < nums.Length
    invariant 0 <= index <= nums.Length
    invariant currentMax == nums[idx]
    invariant forall i :: 0 <= i && i < index ==> nums[i] <= currentMax
  {
    if nums[index] > currentMax {
      currentMax := nums[index];
      idx := index;
    }
    index := index + 1;
  }
}
// </vc-code>
