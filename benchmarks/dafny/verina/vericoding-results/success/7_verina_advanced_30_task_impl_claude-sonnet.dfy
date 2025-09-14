// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LongestIncreasingStreak(nums: array<int>) returns (result: nat)
    ensures
        (nums.Length == 0 ==> result == 0) &&
        result <= nums.Length
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): fixed loop invariant by ensuring maxStreak bounds are properly maintained */
  if nums.Length == 0 {
    result := 0;
    return;
  }
  
  var maxStreak := 1;
  var currentStreak := 1;
  var i := 1;
  
  while i < nums.Length
    invariant 1 <= i <= nums.Length
    invariant currentStreak >= 1
    invariant maxStreak >= 1
    invariant maxStreak <= i
    invariant maxStreak >= currentStreak
  {
    if nums[i] > nums[i-1] {
      currentStreak := currentStreak + 1;
    } else {
      currentStreak := 1;
    }
    
    if currentStreak > maxStreak {
      maxStreak := currentStreak;
    }
    
    i := i + 1;
  }
  
  result := maxStreak;
}
// </vc-code>
