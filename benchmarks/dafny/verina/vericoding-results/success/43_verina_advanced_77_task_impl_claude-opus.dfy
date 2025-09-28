// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Max(a: nat, b: nat): nat { if a > b then a else b }

function ComputeWater(height: array<nat>, i: nat): nat
  requires 0 <= i < height.Length
  reads height
{
  var leftMax := ComputeLeftMax(height, i);
  var rightMax := ComputeRightMax(height, i);
  var minHeight := if leftMax < rightMax then leftMax else rightMax;
  if minHeight > height[i] then minHeight - height[i] else 0
}

function ComputeLeftMax(height: array<nat>, i: nat): nat
  requires 0 <= i < height.Length
  reads height
  decreases i
{
  if i == 0 then height[0]
  else Max(height[i], ComputeLeftMax(height, i - 1))
}

function ComputeRightMax(height: array<nat>, i: nat): nat
  requires 0 <= i < height.Length
  reads height
  decreases height.Length - i
{
  if i == height.Length - 1 then height[i]
  else Max(height[i], ComputeRightMax(height, i + 1))
}

function SumWater(height: array<nat>, i: nat): nat
  requires 0 <= i <= height.Length
  reads height
  decreases i
{
  if i == 0 then 0
  else ComputeWater(height, i - 1) + SumWater(height, i - 1)
}
// </vc-helpers>

// <vc-spec>
method TrapRainWater(height: array<nat>) returns (result: nat)
    requires height.Length >= 0
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  if height.Length == 0 {
    result := 0;
  } else {
    result := SumWater(height, height.Length);
  }
}
// </vc-code>
