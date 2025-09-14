// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): kept the max function as it's useful */function max(a: int, b: int): int { if a > b then a else b }
// </vc-helpers>

// <vc-spec>
method LongestIncreasingStreak(nums: array<int>) returns (result: nat)
    ensures
        (nums.Length == 0 ==> result == 0) &&
        result <= nums.Length
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): added invariant for current <= i, declared vars as nat */
{
  if nums.Length == 0 {
    result := 0;
    return;
  }
  var maxStreak: nat := 0;
  var current: nat := 1;
  var i: nat := 1;
  while i < nums.Length
    invariant 0 < i <= nums.Length
    invariant maxStreak <= nums.Length
    invariant current >= 1
    invariant current <= i
  {
    if nums[i] > nums[i - 1] {
      current := current + 1;
    } else {
      maxStreak := max(maxStreak, current);
      current := 1;
    }
    i := i + 1;
  }
  maxStreak := max(maxStreak, current);
  result := maxStreak;
}
// </vc-code>
