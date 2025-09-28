// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause to allow array element access */
predicate HasPair(nums: array<int>, target: int) reads nums {
  exists i: int, j: int :: 0 <= i < j < nums.Length && nums[i] + nums[j] == target
}

// </vc-helpers>

// <vc-spec>
method TwoSum(nums: array<int>, target: int) returns (result: (int, int))
    requires
        nums.Length > 1 &&
        exists i: int, j: int :: 0 <= i < j < nums.Length && nums[i] + nums[j] == target
    ensures
        0 <= result.0 < result.1 < nums.Length &&
        nums[result.0] + nums[result.1] == target
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): choose indices satisfying precondition nondeterministically */
  var i, j :| 0 <= i < j < nums.Length && nums[i] + nums[j] == target;
  result := (i, j);
}

// </vc-code>
