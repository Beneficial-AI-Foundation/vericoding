// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: nat, b: nat): nat { if a > b then a else b }
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
    } else {
        var max_streak: nat := 1;
        var current_streak: nat := 1;
        var i: nat := 1;
        while i < nums.Length
            invariant 1 <= i <= nums.Length
            invariant 1 <= current_streak
            invariant 1 <= max_streak
            invariant max_streak <= i
            invariant current_streak <= i
        {
            if nums[i] > nums[i-1] {
                current_streak := current_streak + 1;
            } else {
                current_streak := 1;
            }
            max_streak := max(max_streak, current_streak);
            i := i + 1;
        }
        result := max_streak;
    }
}
// </vc-code>
