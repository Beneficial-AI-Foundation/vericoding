// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
function max(a: int, b: int): int { if a < b then b else a }
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
    var best: nat := 1;
    var curr: nat := 1;
    var i: int := 1;
    while i < nums.Length
      invariant 1 <= i <= nums.Length
      invariant 1 <= curr <= i
      invariant 1 <= best <= i
    {
      if nums[i] > nums[i - 1] {
        curr := curr + 1;
      } else {
        curr := 1;
      }
      if curr > best {
        best := curr;
      }
      i := i + 1;
    }
    result := best;
  }
}
// </vc-code>
