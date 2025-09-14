// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method twoSum(nums: array<int>, target: int) returns (i: int, j: int)
  requires nums.Length > 1
  requires exists i,j::0 <= i < j < nums.Length &&  nums[i] + nums[j] == target
  ensures 0 <= i < j < nums.Length && nums[i] + nums[j] == target
  ensures forall ii,jj:: (0 <= ii < i && ii < jj < nums.Length)  ==> nums[ii] + nums[jj] != target
  ensures forall jj:: i < jj < j ==> nums[i] + nums[jj] != target
// </vc-spec>
// <vc-code>
{
  var i_idx := 0;
  while i_idx < nums.Length
    invariant 0 <= i_idx <= nums.Length
    invariant forall i1, j1 :: 0 <= i1 < i_idx && i1 < j1 < nums.Length ==> nums[i1] + nums[j1] != target
  {
    var j_idx := i_idx + 1;
    while j_idx < nums.Length
      invariant 0 <= i_idx < nums.Length
      invariant i_idx + 1 <= j_idx <= nums.Length
      invariant forall i1, j1 :: 0 <= i1 < i_idx && i1 < j1 < nums.Length ==> nums[i1] + nums[j1] != target
      invariant forall j1 :: i_idx < j1 < j_idx ==> nums[i_idx] + nums[j1] != target
    {
      if nums[i_idx] + nums[j_idx] == target {
        i := i_idx;
        j := j_idx;
        return;
      }
      j_idx := j_idx + 1;
    }
    i_idx := i_idx + 1;
  }
}
// </vc-code>
