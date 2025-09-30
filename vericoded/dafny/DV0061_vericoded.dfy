// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function MaxLeft(heights: array<int>, i: int): int
  requires 0 <= i < heights.Length
  reads heights
  decreases i
{
  if i == 0 then heights[0]
  else max(MaxLeft(heights, i-1), heights[i])
}

function MaxRight(heights: array<int>, i: int): int
  requires 0 <= i < heights.Length
  reads heights
  decreases heights.Length - i
{
  if i == heights.Length - 1 then heights[i]
  else max(heights[i], MaxRight(heights, i+1))
}

function max(a: int, b: int): int
{
  if a > b then a else b
}

function min(a: int, b: int): int
{
  if a < b then a else b
}
// </vc-helpers>

// <vc-spec>
method Rain(heights: array<int>) returns (result: int)
    requires forall i :: 0 <= i < heights.Length ==> heights[i] >= 0
    ensures result >= 0
    ensures heights.Length < 3 ==> result == 0
// </vc-spec>
// <vc-code>
{
  if heights.Length < 3 {
    result := 0;
    return;
  }
  
  result := 0;
  var i := 0;
  
  while i < heights.Length
    invariant 0 <= i <= heights.Length
    invariant result >= 0
  {
    var leftMax := MaxLeft(heights, i);
    var rightMax := MaxRight(heights, i);
    var water := min(leftMax, rightMax) - heights[i];
    if water > 0 {
      result := result + water;
    }
    i := i + 1;
  }
}
// </vc-code>
