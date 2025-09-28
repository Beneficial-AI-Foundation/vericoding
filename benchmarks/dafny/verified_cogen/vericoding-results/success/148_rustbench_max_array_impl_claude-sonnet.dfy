// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed incorrect lemma that wasn't needed */
predicate IsMaxIndex(nums: array<int>, idx: int)
  reads nums
{
  0 <= idx < nums.Length &&
  forall i :: 0 <= i < nums.Length ==> nums[i] <= nums[idx]
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
  /* code modified by LLM (iteration 2): fixed loop invariant to ensure postcondition */
  idx := 0;
  var i := 1;
  
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant 0 <= idx < nums.Length
    invariant forall k :: 0 <= k < i ==> nums[k] <= nums[idx]
  {
    if nums[i] > nums[idx] {
      idx := i;
    }
    i := i + 1;
  }
}
// </vc-code>
