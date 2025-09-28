// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): refined predicate for no target-summing pairs before index k */
predicate NoPairBefore(nums: array<int>, target: int, k: int)
    reads nums
{
  forall i: int, j: int :: 0 <= i < j < nums.Length && i < k ==> nums[i] + nums[j] != target
}

/* helper modified by LLM (iteration 3): removed invalid reads clause and null check; step lemma to extend NoPairBefore from i to i+1 */
lemma NoPairBeforeStep(nums: array<int>, target: int, i: int)
    requires 0 <= i < nums.Length - 1
    requires NoPairBefore(nums, target, i)
    requires forall j: int :: i < j < nums.Length ==> nums[i] + nums[j] != target
    ensures NoPairBefore(nums, target, i + 1)
{
  forall i0: int, j0: int
    | 0 <= i0 < j0 < nums.Length && i0 < i + 1
    ensures nums[i0] + nums[j0] != target
  {
    if i0 < i {
      assert nums[i0] + nums[j0] != target; // from NoPairBefore(nums, target, i)
    } else {
      assert i0 == i;
      assert i < j0 < nums.Length;
      assert nums[i] + nums[j0] != target;
      assert nums[i0] + nums[j0] != target;
    }
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
  /* code modified by LLM (iteration 3): verified nested search with minimal first index using helper lemma */
  var n := nums.Length;
  var i := 0;
  // Initially vacuously true: no pair before index 0
  assert NoPairBefore(nums, target, i);
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant NoPairBefore(nums, target, i)
    decreases n - 1 - i
  {
    var j := i + 1;
    while j < n
      invariant i + 1 <= j <= n
      invariant 0 <= i < n
      invariant forall k: int :: i < k < j ==> nums[i] + nums[k] != target
      decreases n - j
    {
      if nums[i] + nums[j] == target {
        result := (i, j);
        return;
      } else {
        j := j + 1;
      }
    }
    assert j == n;
    // From the inner-loop invariant at j == n, we get the premise for the step lemma
    assert forall k: int :: i < k < n ==> nums[i] + nums[k] != target;
    NoPairBeforeStep(nums, target, i);
    i := i + 1;
  }
  // By precondition, a pair must exist; derive contradiction to show this point is unreachable
  assert i == n - 1;
  var ii: int, jj: int :| 0 <= ii < jj < n && nums[ii] + nums[jj] == target;
  assert ii < n - 1; // since ii < jj < n
  assert NoPairBefore(nums, target, i);
  assert 0 <= ii < jj < n && ii < i;
  assert nums[ii] + nums[jj] != target; // from NoPairBefore
  assert nums[ii] + nums[jj] == target; // from choice
  assert false;
}
// </vc-code>
