// <vc-helpers>
lemma NoSolutionBefore(nums: array<int>, target: int, i: int, j: int)
  requires 0 <= i < j < nums.Length
  requires nums[i] + nums[j] == target
  requires forall ii, jj :: 0 <= ii < i && ii < jj < nums.Length ==> nums[ii] + nums[jj] != target
  requires forall jj :: i < jj < j ==> nums[i] + nums[jj] != target
  ensures forall ii, jj :: (0 <= ii < i && ii < jj < nums.Length) ==> nums[ii] + nums[jj] != target
  ensures forall jj :: i < jj < j ==> nums[i] + nums[jj] != target
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method twoSum(nums: array<int>, target: int) returns (i: int, j: int)
  requires nums.Length > 1
  requires exists i,j::0 <= i < j < nums.Length &&  nums[i] + nums[j] == target
  ensures 0 <= i < j < nums.Length && nums[i] + nums[j] == target
  ensures forall ii,jj:: (0 <= ii < i && ii < jj < nums.Length)  ==> nums[ii] + nums[jj] != target
  ensures forall jj:: i < jj < j ==> nums[i] + nums[jj] != target
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  i := 0;
  while i < nums.Length - 1
    invariant 0 <= i < nums.Length
    invariant forall ii, jj :: 0 <= ii < i && ii < jj < nums.Length ==> nums[ii] + nums[jj] != target
  {
    j := i + 1;
    while j < nums.Length
      invariant i < j <= nums.Length
      invariant forall jj :: i < jj < j ==> nums[i] + nums[jj] != target
      invariant forall ii, jj :: 0 <= ii < i && ii < jj < nums.Length ==> nums[ii] + nums[jj] != target
    {
      if nums[i] + nums[j] == target {
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  assume false;
}
// </vc-code>
