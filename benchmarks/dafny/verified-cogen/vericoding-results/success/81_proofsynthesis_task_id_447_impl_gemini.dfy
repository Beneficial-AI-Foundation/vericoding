// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CubeElement(nums: array<int>) returns (cubed: array<int>)

    requires
        forall k :: 0 <= k < nums.Length ==> (
            var val := nums[k];
            var squared := val * val;
            var cubed_val := squared * val;
            -2147483648 <= squared <= 2147483647 &&
            -2147483648 <= cubed_val <= 2147483647
        )

    ensures
        cubed.Length == nums.Length
    ensures
        forall i :: 0 <= i < nums.Length ==> 
            cubed[i] == nums[i] * nums[i] * nums[i]
// </vc-spec>
// <vc-code>
{
  cubed := new int[nums.Length];
  var i := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant cubed.Length == nums.Length
    invariant forall j :: 0 <= j < i ==> cubed[j] == nums[j] * nums[j] * nums[j]
  {
    cubed[i] := nums[i] * nums[i] * nums[i];
    i := i + 1;
  }
}
// </vc-code>
