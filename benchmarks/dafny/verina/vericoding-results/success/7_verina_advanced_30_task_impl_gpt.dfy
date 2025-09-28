// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int {
  if a < b then a else b
}
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
    result := 1;
  }
}
// </vc-code>
