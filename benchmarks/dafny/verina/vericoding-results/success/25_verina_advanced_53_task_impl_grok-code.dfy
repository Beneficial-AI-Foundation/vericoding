// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
    return 0;
  }
  var minIndex := 0;
  var minVal := nums[0];
  var i := 1;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> nums[j] >= minVal
    invariant minIndex < n && nums[minIndex] == minVal
  {
    if nums[i] < minVal {
      minVal := nums[i];
      minIndex := i;
    }
    i := i + 1;
  }
  i := 0;
  var isValid := true;
  while i < minIndex - 1
    invariant 0 <= i <= minIndex
    invariant isValid ==> true  // placeholder, but actually check in loop
  {
    if nums[i] > nums[i + 1] {
      isValid := false;
    }
    i := i + 1;
  }
  i := minIndex;
  while i < n - 1
    invariant minIndex <= i <= n - 1
    invariant isValid ==> true  // again
  {
    if nums[i] > nums[i + 1] {
      isValid := false;
    }
    i := i + 1;
  }
  if !isValid {
    return -1;
  } else {
    if minIndex == 0 {
      return 0;
    } else {
      return n - minIndex;
    }
  }
}
// </vc-code>
