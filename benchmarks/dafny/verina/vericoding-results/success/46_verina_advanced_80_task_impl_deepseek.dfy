// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

method FindIndices(nums: array<int>, target: int) returns (i: int, j: int)
  requires 
    nums.Length >= 2 &&
    (exists x: int, y: int :: 0 <= y < x < nums.Length && nums[x] + nums[y] == target) &&
    (forall a: int, b: int, c: int, d: int :: 
      (0 <= b < a < nums.Length && nums[a] + nums[b] == target &&
       0 <= d < c < nums.Length && nums[c] + nums[d] == target) ==> 
      (a == c && b == d))
  ensures 
    0 <= j < i < nums.Length && nums[i] + nums[j] == target
{
  i := nums.Length - 1;
  while i >= 1
    decreases i
    invariant -1 <= i < nums.Length
    invariant !(exists k: int :: 0 <= k < nums.Length && (exists l: int :: 0 <= l < k && nums[k] + nums[l] == target) && k > i)
  {
    j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant forall l: int :: 0 <= l < j ==> nums[i] + nums[l] != target
      decreases i - j
    {
      if nums[i] + nums[j] == target {
        return;
      }
      j := j + 1;
    }
    i := i - 1;
  }
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
  var i: int, j: int;
  i, j := FindIndices(nums, target);
  result := new int[2];
  result[0] := j;
  result[1] := i;
}
// </vc-code>
