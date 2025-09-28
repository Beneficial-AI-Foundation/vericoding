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
  /* code modified by LLM (iteration 4): add loop invariants to ensure result <= nums.Length */
  if nums.Length == 0 {
    result := 0;
  } else {
    var maxStreak := 1;
    var current := 1;
    var i := 1;
    while i < nums.Length
      invariant 0 <= i <= nums.Length
      invariant current >= 1
      invariant maxStreak >= 1
      invariant current <= i
      invariant maxStreak <= nums.Length
    {
      if nums[i] > nums[i-1] {
        current := current + 1;
        if current > maxStreak {
          maxStreak := current;
        }
      } else {
        current := 1;
      }
      i := i + 1;
    }
    result := maxStreak;
  }
}
// </vc-code>
