// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int { if a > b then a else b }
// </vc-helpers>

// <vc-spec>
method LongestIncreasingStreak(nums: array<int>) returns (result: nat)
    ensures
        (nums.Length == 0 ==> result == 0) &&
        result <= nums.Length
// </vc-spec>
// <vc-code>
{
  var current_streak_length := if nums.Length > 0 then 1 else 0;
  result := if nums.Length > 0 then 1 else 0;
  
  if nums.Length > 1 {
    var i := 1;
    while i < nums.Length
      invariant 1 <= i <= nums.Length
      invariant current_streak_length >= 1 && result >= 1
      invariant result <= i
      invariant result >= current_streak_length
      decreases nums.Length - i
    {
      if nums[i] > nums[i-1] {
        current_streak_length := current_streak_length + 1;
        result := max(result, current_streak_length);
      } else {
        current_streak_length := 1;
      }
      i := i + 1;
    }
  }
}
// </vc-code>
