// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added decreases clause to MaxRight for termination proof */
function MaxLeft(height: array<nat>, i: nat): nat
  requires 0 <= i < height.Length
  reads height
  decreases i
{
  if i == 0 then height[0]
  else max(MaxLeft(height, i-1), height[i])
}

function MaxRight(height: array<nat>, i: nat): nat
  requires 0 <= i < height.Length
  reads height
  decreases height.Length - i
{
  if i == height.Length - 1 then height[i]
  else max(height[i], MaxRight(height, i+1))
}

function max(a: nat, b: nat): nat
{
  if a >= b then a else b
}

function min(a: nat, b: nat): nat
{
  if a <= b then a else b
}
// </vc-helpers>

// <vc-spec>
method TrapRainWater(height: array<nat>) returns (result: nat)
    requires height.Length >= 0
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): No changes needed, implementation is correct */
  result := 0;
  if height.Length <= 2 {
    return result;
  }
  
  var i := 1;
  while i < height.Length - 1
    invariant 1 <= i <= height.Length - 1
    invariant result >= 0
  {
    var leftMax := MaxLeft(height, i-1);
    var rightMax := MaxRight(height, i+1);
    var waterLevel := min(leftMax, rightMax);
    if waterLevel > height[i] {
      result := result + (waterLevel - height[i]);
    }
    i := i + 1;
  }
}
// </vc-code>
