// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: nat, b: nat): nat { if a > b then a else b }
function min(a: nat, b: nat): nat { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method TrapRainWater(height: array<nat>) returns (result: nat)
    requires height.Length >= 0
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var n := height.Length;
  result := 0;
  if n < 2 {
    return;
  }
  var l := 0;
  var r := n - 1;
  var leftMax: nat := 0;
  var rightMax: nat := 0;
  while l < r
    invariant 0 <= l < n
    invariant 0 <= r < n
    invariant result >= 0
    invariant leftMax >= 0
    invariant rightMax >= 0
    decreases r - l
  {
    if height[l] <= height[r] {
      if height[l] >= leftMax {
        leftMax := height[l];
      } else {
        result := result + (leftMax - height[l]);
      }
      l := l + 1;
    } else {
      if height[r] >= rightMax {
        rightMax := height[r];
      } else {
        result := result + (rightMax - height[r]);
      }
      r := r - 1;
    }
  }
}

// </vc-code>
