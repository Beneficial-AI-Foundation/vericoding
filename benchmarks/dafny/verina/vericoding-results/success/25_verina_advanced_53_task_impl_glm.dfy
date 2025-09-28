// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
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
  var minIndex := 0;
  var minValue := nums[0];
  for i := 1 to n
    invariant 0 <= minIndex < n
    invariant minValue == nums[minIndex]
    invariant forall j :: 0 <= j < i ==> nums[j] >= minValue
  {
    if nums[i] < minValue {
      minValue := nums[i];
      minIndex := i;
    }
  }
  result := minIndex;
}
// </vc-code>
