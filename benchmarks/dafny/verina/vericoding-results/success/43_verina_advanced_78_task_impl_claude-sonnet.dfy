// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate ValidPair(nums: array<int>, target: int, i: int, j: int)
  reads nums
{
  0 <= i < j < nums.Length && nums[i] + nums[j] == target
}

/* helper modified by LLM (iteration 3): Fixed lemma syntax by removing ghost from returns */
lemma FindValidPair(nums: array<int>, target: int) returns (i: int, j: int)
  requires nums.Length > 1
  requires exists x: int, y: int :: 0 <= x < y < nums.Length && nums[x] + nums[y] == target
  ensures 0 <= i < j < nums.Length && nums[i] + nums[j] == target
{
  var x :| exists y :: 0 <= x < y < nums.Length && nums[x] + nums[y] == target;
  var y :| 0 <= x < y < nums.Length && nums[x] + nums[y] == target;
  i, j := x, y;
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
  /* code modified by LLM (iteration 3): Fixed loop invariants and ensured valid pair is found */
  var i := 0;
  while i < nums.Length - 1
    invariant 0 <= i <= nums.Length - 1
    invariant exists x: int, y: int :: 0 <= x < y < nums.Length && nums[x] + nums[y] == target
    invariant forall x: int, y: int :: 0 <= x < nums.Length && x < i && x < y < nums.Length ==> nums[x] + nums[y] != target
  {
    var j := i + 1;
    while j < nums.Length
      invariant i + 1 <= j <= nums.Length
      invariant exists x: int, y: int :: 0 <= x < y < nums.Length && nums[x] + nums[y] == target
      invariant forall y: int :: i < y < j ==> nums[i] + nums[y] != target
    {
      if nums[i] + nums[j] == target {
        result := (i, j);
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  assert false;
  result := (0, 1);
}
// </vc-code>
