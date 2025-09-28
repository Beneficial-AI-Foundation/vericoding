// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function MultiplyBy3(n: int): int { n * n * n }

lemma MultiplyBy3WithinBounds(n: int)
  requires -2147483648 <= n * n <= 2147483647
  requires -2147483648 <= n * n * n <= 2147483647
  ensures -2147483648 <= MultiplyBy3(n) <= 2147483647
{
}

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
  var index := 0;

  while index < nums.Length
    invariant 0 <= index <= nums.Length
    invariant cubed.Length == nums.Length
    invariant forall j :: 0 <= j < index ==> cubed[j] == nums[j] * nums[j] * nums[j]
  {
    cubed[index] := nums[index] * nums[index] * nums[index];
    index := index + 1;
  }
}
// </vc-code>
