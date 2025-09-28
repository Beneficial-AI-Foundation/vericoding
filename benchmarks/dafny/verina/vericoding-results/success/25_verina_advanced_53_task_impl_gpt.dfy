// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function MinInt(x: int, y: int): int { if x < y then x else y }
// </vc-helpers>

// <vc-spec>
method MinimumRightShifts(nums: array<int>) returns (result: int)
    requires nums.Length <= 2147483647
    requires forall i, j :: 0 <= i < nums.Length && 0 <= j < nums.Length && i != j ==> nums[i] != nums[j]
    ensures
        var n := nums.Length;
        if n <= 1 then
            result == 0
        else
            (result >= 0 && result < n) || result == -1
// </vc-spec>
// <vc-code>
{
  var n := nums.Length;
  if n <= 1 {
    result := 0;
    return;
  }
  var drops := 0;
  var idx := 0;
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant 0 <= drops
    invariant 0 <= idx <= n - 2
    decreases n - 1 - i
  {
    if nums[i] > nums[i + 1] {
      drops := drops + 1;
      idx := i;
    }
    i := i + 1;
  }
  if drops == 0 {
    result := 0;
  } else if drops == 1 && nums[n - 1] < nums[0] {
    assert idx <= n - 2;
    result := idx + 1;
  } else {
    result := -1;
  }
}
// </vc-code>
