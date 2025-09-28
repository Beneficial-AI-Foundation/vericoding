// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Max(a: nat, b: nat): nat { if a >= b then a else b }

function Min(a: nat, b: nat): nat { if a <= b then a else b }
// </vc-helpers>

// <vc-spec>
method TrapRainWater(height: array<nat>) returns (result: nat)
    requires height.Length >= 0
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var n := height.Length;
  var left := 0;
  var right := if n == 0 then -1 else n - 1;
  var leftMax: nat := 0;
  var rightMax: nat := 0;
  result := 0;
  while left <= right
    invariant 0 <= left <= n
    invariant -1 <= right < n
    invariant 0 <= leftMax
    invariant 0 <= rightMax
    invariant result >= 0
  {
    if height[left] <= height[right] {
      if height[left] >= leftMax {
        leftMax := height[left];
      } else {
        result := result + leftMax - height[left];
      }
      left := left + 1;
    } else {
      if height[right] >= rightMax {
        rightMax := height[right];
      } else {
        result := result + rightMax - height[right];
      }
      right := right - 1;
    }
  }
}
// </vc-code>
