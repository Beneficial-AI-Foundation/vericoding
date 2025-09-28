// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): recursive search for j index matching target with given i */
method FindJ(nums: array<int>, target: int, i: int, j: int) returns (k: int)
  requires 0 <= i < nums.Length
  requires i < j < nums.Length
  requires exists b: int :: j <= b < nums.Length && nums[i] + nums[b] == target
  ensures j <= k < nums.Length
  ensures nums[i] + nums[k] == target
  decreases nums.Length - j
{
  if nums[i] + nums[j] == target {
    k := j;
    return;
  } else {
    k := FindJ(nums, target, i, j + 1);
    return;
  }
}

/* helper modified by LLM (iteration 2): find the first index i that has a matching j and guarantee no valid pairs start before p.0 (for indices >= i) */
method FindFrom(nums: array<int>, target: int, i: int) returns (p: (int,int))
  requires 0 <= i < nums.Length
  requires exists a,b :: i <= a < b < nums.Length && nums[a] + nums[b] == target
  ensures i <= p.0 < p.1 < nums.Length
  ensures nums[p.0] + nums[p.1] == target
  ensures forall a,b :: i <= a < b < nums.Length && a < p.0 ==> nums[a] + nums[b] != target
  decreases nums.Length - i
{
  if exists j: int :: i < j < nums.Length && nums[i] + nums[j] == target {
    var k := FindJ(nums, target, i, i + 1);
    p := (i, k);
    return;
  } else {
    p := FindFrom(nums, target, i + 1);
    return;
  }
}
// </vc-helpers>

// <vc-spec>
method TwoSum(nums: array<int>, target: int) returns (result: (int, int))
    requires 
        nums.Length > 1 &&
        (exists i: int, j: int :: 0 <= i < j < nums.Length && nums[i] + nums[j] == target)
    ensures
        0 <= result.0 < result.1 < nums.Length &&
        nums[result.0] + nums[result.1] == target &&
        (forall i: int, j: int :: 0 <= i < j < nums.Length && i < result.0 ==> nums[i] + nums[j] != target)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): call helper to find the earliest valid pair starting from index 0 */
  var p := FindFrom(nums, target, 0);
  result := p;
}
// </vc-code>
