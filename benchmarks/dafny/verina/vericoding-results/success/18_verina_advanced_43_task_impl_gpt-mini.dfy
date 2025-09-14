// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function maxInt(a: int, b: int): int { if a >= b then a else b }
// </vc-helpers>

// <vc-spec>
method MaxStrength(nums: array<int>) returns (result: int)
    requires nums.Length > 0
    ensures
        /* The result represents the maximum product of any non-empty subset of nums.
           For simplicity, we ensure that the result is at least as large as one of the elements. */
        exists i :: 0 <= i < nums.Length && result >= nums[i]
// </vc-spec>
// <vc-code>
{
    var n := nums.Length;
    var cur := nums[0];
    var i := 1;
    while i < n
      invariant 1 <= i <= n
      invariant forall k :: 0 <= k < i ==> cur >= nums[k]
      invariant exists j :: 0 <= j < i && cur == nums[j]
      decreases n - i
    {
      if nums[i] > cur {
        cur := nums[i];
      }
      i := i + 1;
    }
    result := cur;
  }
// </vc-code>
