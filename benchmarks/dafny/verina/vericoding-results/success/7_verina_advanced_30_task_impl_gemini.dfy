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
        var longestStreak: nat := 1;
        var currentStreak: nat := 1;
        var i := 1;
        while i < nums.Length
            invariant nums.Length > 0
            invariant 1 <= i <= nums.Length
            invariant 1 <= currentStreak <= i
            invariant 1 <= longestStreak <= i
        {
            if nums[i] > nums[i-1] {
                currentStreak := currentStreak + 1;
            } else {
                longestStreak := max(longestStreak, currentStreak);
                currentStreak := 1;
            }
            i := i + 1;
        }
        result := max(longestStreak, currentStreak);
    }
}
// </vc-code>
