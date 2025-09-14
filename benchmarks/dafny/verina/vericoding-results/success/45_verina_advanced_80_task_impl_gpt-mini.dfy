// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): predicate Pair now declares reads clause to allow reading array elements */
predicate Pair(nums: array<int>, target: int, i: int, j: int) reads nums { 0 <= j < i < nums.Length && nums[i] + nums[j] == target }
// </vc-helpers>

// <vc-spec>
method TwoSum(nums: array<int>, target: int) returns (result: array<int>)
    requires 
        nums.Length >= 2 &&
        (exists i: int, j: int :: 0 <= j < i < nums.Length && nums[i] + nums[j] == target) &&
        (forall i1: int, j1: int, i2: int, j2: int :: 
            (0 <= j1 < i1 < nums.Length && nums[i1] + nums[j1] == target &&
             0 <= j2 < i2 < nums.Length && nums[i2] + nums[j2] == target) ==> 
            (i1 == i2 && j1 == j2))
    ensures
        result.Length == 2 &&
        0 <= result[0] < nums.Length &&
        0 <= result[1] < nums.Length &&
        result[0] < result[1] &&
        nums[result[0]] + nums[result[1]] == target
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterate pairs and return the unique matching indices; prove contradiction if not found */
  result := new int[2];
  var i := 1;
  while i < nums.Length
    invariant 1 <= i <= nums.Length
    invariant forall ii, jj :: 0 <= jj < ii < i ==> nums[ii] + nums[jj] != target
    decreases nums.Length - i
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant forall jj :: 0 <= jj < j ==> nums[i] + nums[jj] != target
      decreases i - j
    {
      if nums[i] + nums[j] == target {
        result[0] := j;
        result[1] := i;
        return result;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  // At this point, the invariants imply no such pair exists, contradicting the precondition.
  assert i == nums.Length;
  assert forall ii, jj :: 0 <= jj < ii < nums.Length ==> nums[ii] + nums[jj] != target;
  assert !(exists ii, jj :: 0 <= jj < ii < nums.Length && nums[ii] + nums[jj] == target);
  assert false;
}
// </vc-code>
