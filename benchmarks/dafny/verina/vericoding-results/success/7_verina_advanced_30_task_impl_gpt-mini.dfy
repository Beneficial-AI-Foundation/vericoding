// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): trivial lemma that array length is non-negative */
lemma NonNegativeLength<T>(a: array<T>)
    ensures a.Length >= 0
{
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
  /* code modified by LLM (iteration 2): implement longest increasing streak with bounded cur update */
  if nums.Length == 0 {
    result := 0;
    return;
  }
  var max := 1;
  var cur := 1;
  var i := 1;
  while i < nums.Length
    invariant 1 <= cur <= nums.Length
    invariant 1 <= max <= nums.Length
    invariant 1 <= i <= nums.Length
  {
    if nums[i] > nums[i - 1] {
      if cur + 1 <= nums.Length {
        cur := cur + 1;
      } else {
        cur := nums.Length;
      }
    } else {
      if cur > max { max := cur; }
      cur := 1;
    }
    i := i + 1;
  }
  if cur > max { max := cur; }
  result := max;
}
// </vc-code>
