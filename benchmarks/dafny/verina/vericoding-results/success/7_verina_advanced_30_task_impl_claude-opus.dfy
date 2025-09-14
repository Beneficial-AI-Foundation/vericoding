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
  if nums.Length == 0 {
    result := 0;
    return;
  }
  
  var maxStreak := 1;
  var currentStreak := 1;
  var i := 1;
  
  while i < nums.Length
    invariant 1 <= i <= nums.Length
    invariant 1 <= currentStreak <= i
    invariant 1 <= maxStreak <= i
    invariant maxStreak >= currentStreak
  {
    if nums[i] > nums[i-1] {
      currentStreak := currentStreak + 1;
      if currentStreak > maxStreak {
        maxStreak := currentStreak;
      }
    } else {
      currentStreak := 1;
    }
    i := i + 1;
  }
  
  result := maxStreak;
}
// </vc-code>
