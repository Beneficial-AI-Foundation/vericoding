// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Max(a: int, b: int): int { if a >= b then a else b }
function Min(a: int, b: int): int { if a <= b then a else b }
// </vc-helpers>

// <vc-spec>
method Rain(heights: array<int>) returns (result: int)
    requires forall i :: 0 <= i < heights.Length ==> heights[i] >= 0
    ensures result >= 0
    ensures heights.Length < 3 ==> result == 0
// </vc-spec>
// <vc-code>
{
  var n := heights.Length;
  result := 0;
  if n < 3 { return; }
  var l := 0;
  var r := n - 1;
  var leftMax := 0;
  var rightMax := 0;
  while l <= r
    invariant 0 <= l && l <= n
    invariant -1 <= r && r < n
    invariant leftMax >= 0 && rightMax >= 0
    invariant forall i :: 0 <= i && i < l ==> heights[i] <= leftMax
    invariant forall i :: r < i && i < n ==> heights[i] <= rightMax
    invariant result >= 0
    decreases r - l + 1
  {
    if leftMax <= rightMax {
      var h := heights[l];
      if h >= leftMax {
        leftMax := h;
      } else {
        result := result + (leftMax - h);
      }
      l := l + 1;
    } else {
      var h := heights[r];
      if h >= rightMax {
        rightMax := h;
      } else {
        result := result + (rightMax - h);
      }
      r := r - 1;
    }
  }
}
// </vc-code>
