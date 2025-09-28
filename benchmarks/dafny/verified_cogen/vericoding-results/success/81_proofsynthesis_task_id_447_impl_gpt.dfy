// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): provides cube function for element-wise computation */
function cube(x: int): int { x * x * x }
/* helper modified by LLM (iteration 2): predicate for 32-bit bounds used by precondition */
predicate InInt32(x: int) { -2147483648 <= x <= 2147483647 }
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
  /* code modified by LLM (iteration 2): implement element-wise cube with proper loop invariants; removed redundant null-invariant to avoid warning */
  var n := nums.Length;
  cubed := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant cubed.Length == n
    invariant forall j :: 0 <= j < i ==> cubed[j] == nums[j] * nums[j] * nums[j]
    decreases n - i
  {
    var v := nums[i];
    cubed[i] := v * v * v;
    i := i + 1;
  }
}
// </vc-code>
