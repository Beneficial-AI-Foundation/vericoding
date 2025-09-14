// <vc-preamble>
predicate summingPair(i: nat, j: nat, nums: seq<int>, target: int)
    requires i < |nums|
    requires j < |nums|
{
    i != j &&  nums[i] + nums[j] == target
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed invalid reads clause, which is not allowed on value types like seq<int>. */
predicate NoPairsInPrefix(k: nat, nums: seq<int>, target: int)
{
  forall l: nat, m: nat :: l < k && l < m < |nums| ==> !summingPair(l, m, nums, target)
}
// </vc-helpers>

// <vc-spec>
method twoSum(nums: seq<int>, target: int) returns (pair: (nat, nat))
    requires exists i:nat,j:nat :: i < j < |nums| && summingPair(i, j, nums, target) && forall l: nat, m: nat :: l <  m < |nums| && l != i && m != j ==> !summingPair(l, m, nums, target)
    ensures 0 <= pair.0 < |nums| && 0 <= pair.1 < |nums| && summingPair(pair.0, pair.1, nums, target)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): The code logic is correct; the previous failure was a compilation error in the helper predicate. */
  var i: nat := 0;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant NoPairsInPrefix(i, nums, target)
    decreases |nums| - i
  {
    var j: nat := i + 1;
    while j < |nums|
      invariant i < j <= |nums|
      invariant forall m :: i < m < j ==> !summingPair(i, m, nums, target)
      decreases |nums| - j
    {
      if nums[i] + nums[j] == target {
        pair := (i, j);
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  assert false; // Unreachable due to the 'exists' in the requires clause
}
// </vc-code>
