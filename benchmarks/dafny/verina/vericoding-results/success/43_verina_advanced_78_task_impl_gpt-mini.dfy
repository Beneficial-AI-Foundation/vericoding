// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): add reads clause for array access */
predicate PairExists(nums: array<int>, target: int) reads nums { exists i, j :: 0 <= i < j < nums.Length && nums[i] + nums[j] == target }
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
  /* code modified by LLM (iteration 2): iterate i and pick witness pair; return when p == i; fallback uses precondition witness */
  var n := nums.Length;
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant exists p,q :: i <= p < q < n && nums[p] + nums[q] == target
    decreases n - i
  {
    var p,q :| i <= p < q < n && nums[p] + nums[q] == target;
    if p == i {
      result := (i, q);
      return;
    }
    i := i + 1;
  }
  var p,q :| 0 <= p < q < n && nums[p] + nums[q] == target;
  result := (p, q);
}
// </vc-code>
