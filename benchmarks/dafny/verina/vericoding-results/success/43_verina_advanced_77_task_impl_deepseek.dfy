// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed decreases clauses for recursive functions */
function max(a: int, b: int): int { 
    if a > b then a else b 
}

function min(a: int, b: int): int {
    if a < b then a else b
}

function leftMax(height: array<nat>, i: int): int
    reads height
    requires 0 <= i < height.Length
    decreases i
{
    if i == 0 then height[0]
    else max(leftMax(height, i-1), height[i])
}

function rightMax(height: array<nat>, i: int): int
    reads height
    requires 0 <= i < height.Length
    decreases height.Length - i - 1
{
    if i == height.Length - 1 then height[i]
    else max(rightMax(height, i+1), height[i])
}
// </vc-helpers>

// <vc-spec>
method TrapRainWater(height: array<nat>) returns (result: nat)
    requires height.Length >= 0
    ensures result >= 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed water calculation to avoid negative values */
{
    result := 0;
    if height.Length > 0 {
        var i := 0;
        while i < height.Length
            invariant 0 <= i <= height.Length
            invariant result >= 0
            decreases height.Length - i
        {
            var leftM := leftMax(height, i);
            var rightM := rightMax(height, i);
            var waterLevel := min(leftM, rightM);
            var water : nat := 0;
            if waterLevel > height[i] {
                water := waterLevel - height[i];
            }
            result := result + water;
            i := i + 1;
        }
    }
}
// </vc-code>
