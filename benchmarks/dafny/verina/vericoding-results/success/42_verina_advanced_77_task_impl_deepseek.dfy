// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added reads clauses to helper functions */
function max(a: nat, b: nat): nat { if a >= b then a else b }

function LeftMax(height: array<nat>, i: int, j: int): (lm: nat)
  requires 0 <= i <= j < height.Length
  ensures lm >= height[i]
  reads height
  decreases j - i
{
  if i == j then
    height[i]
  else
    max(LeftMax(height, i, j-1), height[j])
}

function RightMax(height: array<nat>, i: int, j: int): (rm: nat)
  requires 0 <= i <= j < height.Length
  ensures rm >= height[j]
  reads height
  decreases j - i
{
  if i == j then
    height[j]
  else
    max(RightMax(height, i+1, j), height[i])
}

function min(a: nat, b: nat): nat { if a <= b then a else b }
// </vc-helpers>

// <vc-spec>
method TrapRainWater(height: array<nat>) returns (result: nat)
    requires height.Length >= 0
    ensures result >= 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Removed redundant right_max recomputation */
{
  if height.Length <= 2 {
    result := 0;
    return;
  }
  
  result := 0;
  var i := 0;
  var left_max: nat := 0;
  var right_max: nat := RightMax(height, 0, height.Length - 1);
  
  while i < height.Length 
    invariant 0 <= i <= height.Length
  {
    if i > 0 {
      left_max := max(left_max, height[i-1]);
    }
    
    var water_level := min(left_max, right_max);
    if water_level > height[i] {
      result := result + (water_level - height[i]);
    }
    
    // Update right_max for next iteration
    if i < height.Length - 1 {
      right_max := RightMax(height, i+1, height.Length - 1);
    } else {
      right_max := 0;
    }
    
    i := i + 1;
  }
}
// </vc-code>
