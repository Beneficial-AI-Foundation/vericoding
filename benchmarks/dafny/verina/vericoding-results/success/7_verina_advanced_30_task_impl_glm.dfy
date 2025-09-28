// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
/* helper modified by LLM (iteration 2): added max function */
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
  /* code modified by LLM (iteration 2): fixed unresolved max by adding helper */
  if nums.Length == 0 {
    result := 0;
    return;
  }
  var currentStreak := 1;
  var maxStreak := 1;
  var i := 1;
  while i < nums.Length
    invariant 1 <= i <= nums.Length
    invariant 1 <= currentStreak <= i
    invariant 1 <= maxStreak <= i
    invariant maxStreak >= currentStreak
  {
    if nums[i] > nums[i-1] {
      currentStreak := currentStreak + 1;
    } else {
      currentStreak := 1;
    }
    maxStreak := max(maxStreak, currentStreak);
    i := i + 1;
  }
  result := maxStreak;
}
// </vc-code>
