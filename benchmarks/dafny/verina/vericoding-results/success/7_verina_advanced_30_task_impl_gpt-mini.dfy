// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Max(a: int, b: int): int { if a > b then a else b }
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
  var n := nums.Length;
  var best := 1;
  var cur := 1;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant 1 <= cur <= i
    invariant 1 <= best <= n
    decreases n - i
  {
    if nums[i] > nums[i - 1] {
      cur := cur + 1;
    } else {
      cur := 1;
    }
    if cur > best {
      best := cur;
    }
    i := i + 1;
  }
  result := best;
}
// </vc-code>
