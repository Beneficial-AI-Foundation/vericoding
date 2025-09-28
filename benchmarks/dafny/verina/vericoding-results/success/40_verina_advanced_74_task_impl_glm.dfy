// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solution(nums: array<int>) returns (result: int)
    requires
        1 <= nums.Length <= 100
    requires
        forall i :: 0 <= i < nums.Length ==> nums[i] >= 1 && nums[i] <= 100
    ensures
        result >= 0
// </vc-spec>
// <vc-code>
{
  var total := 0;
  for i := 0 to nums.Length
      invariant total >= 0
  {
    total := total + nums[i];
  }
  result := total;
}
// </vc-code>
