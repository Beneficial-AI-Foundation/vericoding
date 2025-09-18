// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int
{
  if a >= b then a else b
}
// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(nums: array<int>) returns (result: int)
    ensures result >= 0
    ensures result <= nums.Length
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fixed inner loop invariant by tracking currentLength correctly */
  if nums.Length == 0 {
    result := 0;
    return;
  }
  
  var maxLength := 1;
  var i := 0;
  
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant maxLength >= 1
    invariant maxLength <= nums.Length
  {
    var currentLength := 1;
    var j := i + 1;
    
    while j < nums.Length && nums[j] > nums[j-1]
      invariant i < j <= nums.Length
      invariant currentLength >= 1
      invariant currentLength <= j - i
      invariant currentLength <= nums.Length
    {
      currentLength := currentLength + 1;
      j := j + 1;
    }
    
    if currentLength > maxLength {
      maxLength := currentLength;
    }
    i := i + 1;
  }
  
  result := maxLength;
}
// </vc-code>
