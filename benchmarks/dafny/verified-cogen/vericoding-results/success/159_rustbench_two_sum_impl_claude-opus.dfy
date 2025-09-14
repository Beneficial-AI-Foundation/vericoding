// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method TwoSum(nums: array<int>, target: int) returns (result: (int, int))
    requires
        nums.Length >= 2
    requires
        exists i: int, j: int :: 0 <= i < j < nums.Length && nums[i] + nums[j] == target
    requires
        forall i: int, j: int ::
            (0 <= i < nums.Length && 0 <= j < nums.Length)
                ==> (nums[i] + nums[j] <= 2147483647
                    && nums[i] + nums[j] >= -2147483648)
    ensures
        var (i, j) := result; 0 <= i < nums.Length
    ensures
        var (i, j) := result; 0 <= j < nums.Length
    ensures
        var (i, j) := result; i != j
    ensures
        var (i, j) := result; nums[i] + nums[j] == target
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant forall x, y :: 0 <= x < i && 0 <= y < nums.Length && x != y ==> nums[x] + nums[y] != target
  {
    var j := 0;
    while j < nums.Length
      invariant 0 <= j <= nums.Length
      invariant forall y :: 0 <= y < j && i != y ==> nums[i] + nums[y] != target
    {
      if i != j && nums[i] + nums[j] == target {
        return (i, j);
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return (0, 0);
}
// </vc-code>
