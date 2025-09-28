// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): add bounds check to avoid out-of-range access */
predicate HasPairInPrefix(nums: array<int>, target: int, i: int) reads nums {
  0 <= i < nums.Length &&
  exists i1, j1 :: 0 <= j1 < i1 <= i && nums[i1] + nums[j1] == target
}
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
  /* code modified by LLM (iteration 2): iterate prefixes forward and search for matching j to ensure invariants are maintainable */
  result := new int[2];
  var i := 1;
  while i < nums.Length
    invariant 1 <= i <= nums.Length
    invariant forall i1, j1 :: 0 <= j1 < i1 < i ==> nums[i1] + nums[j1] != target
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant i < nums.Length
      invariant forall j1 :: 0 <= j1 < j ==> nums[i] + nums[j1] != target
    {
      if nums[i] + nums[j] == target {
        result[0] := j;
        result[1] := i;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  // Fallback to satisfy verifier; precondition guarantees we never reach here
  result[0] := 0;
  result[1] := 1;
}

// </vc-code>
