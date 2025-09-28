// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma LinearSearchLemma(nums: array<int>, target: int, j: int)
  requires 0 <= j <= nums.Length
  ensures forall i :: 0 <= i < j ==> nums[i] != target || (exists k :: 0 <= k < j && nums[k] == target)
{
  if j > 0 {
    LinearSearchLemma(nums, target, j - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method LinearSearch(nums: array<int>, target: int) returns (ret: int)
    requires nums.Length < 0x8000_0000
    ensures ret < nums.Length
    ensures ret >= 0 ==> nums[ret] == target
    ensures ret >= 0 ==> forall i :: 0 <= i < ret ==> nums[i] != target
    ensures ret < 0 ==> forall i :: 0 <= i < nums.Length ==> nums[i] != target
// </vc-spec>
// <vc-code>
{
  var index := 0;
  while index < nums.Length
    invariant 0 <= index <= nums.Length
    invariant forall i :: 0 <= i < index ==> nums[i] != target
  {
    if nums[index] == target {
      ret := index;
      return;
    }
    index := index + 1;
  }
  ret := -1;
}
// </vc-code>
