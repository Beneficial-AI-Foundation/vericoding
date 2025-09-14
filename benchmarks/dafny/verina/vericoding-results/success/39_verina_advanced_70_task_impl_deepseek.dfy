// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsSemiOrdered(nums: array<int>, i: int, j: int): bool
  requires 0 <= i <= j < nums.Length
  reads nums
  decreases j - i
{
  if i == j then
    true
  else if i + 1 == j then
    nums[i] <= nums[j]
  else
    nums[i] <= nums[i+1] && IsSemiOrdered(nums, i+1, j)
}
// </vc-helpers>

// <vc-spec>
method SemiOrderedPermutation(nums: array<int>) returns (result: int)
    ensures 
        result >= 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed compilation errors and added termination measure */
  var n := nums.Length;
  if n == 0 {
    result := 0;
    return;
  }
  
  result := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result >= 0
  {
    var j := i;
    while j < n
      invariant i <= j <= n
      invariant result >= 0
      decreases n - j
    {
      if IsSemiOrdered(nums, i, j) {
        result := result + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
