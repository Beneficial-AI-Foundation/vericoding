// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsSorted(nums: array<int>, start: int, end: int): bool
  requires 0 <= start <= end <= nums.Length
  reads nums
{
  forall i, j :: start <= i < j < end ==> nums[i] < nums[j]
}

/* helper modified by LLM (iteration 3): Fixed rotation check logic */
function IsRotationSorted(nums: array<int>, k: int): bool
  requires 0 <= k < nums.Length
  reads nums
{
  var n := nums.Length;
  if n <= 1 then true
  else if k == 0 then
    forall i :: 0 <= i < n - 1 ==> nums[i] < nums[i + 1]
  else
    (forall i :: k <= i < n - 1 ==> nums[i] < nums[i + 1]) &&
    (forall i :: 0 <= i < k - 1 ==> nums[i] < nums[i + 1]) &&
    nums[n - 1] < nums[0]
}
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
/* code modified by LLM (iteration 3): Fixed postcondition and termination */
{
  var n := nums.Length;
  if n <= 1 {
    result := 0;
  } else {
    var found := false;
    var k := 0;
    result := -1;
    while k < n
      decreases n - k
      invariant 0 <= k <= n
      invariant !found ==> result == -1
      invariant found ==> 0 <= result < n && IsRotationSorted(nums, result)
      invariant !found ==> forall j :: 0 <= j < k ==> !IsRotationSorted(nums, j)
    {
      if IsRotationSorted(nums, k) {
        found := true;
        result := k;
        break;
      }
      k := k + 1;
    }
  }
}
// </vc-code>
