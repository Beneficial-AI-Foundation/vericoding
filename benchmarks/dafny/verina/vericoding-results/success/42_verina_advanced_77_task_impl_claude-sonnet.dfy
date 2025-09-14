// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: nat, b: nat): nat { if a > b then a else b }

function min(a: nat, b: nat): nat { if a < b then a else b }

/* helper modified by LLM (iteration 2): added decreases clause to fix termination proof */
function maxLeft(height: array<nat>, i: nat): nat
    requires i < height.Length
    reads height
    decreases i
{
    if i == 0 then height[0]
    else max(height[i], maxLeft(height, i-1))
}

/* helper modified by LLM (iteration 2): added decreases clause to fix termination proof */
function maxRight(height: array<nat>, i: nat): nat
    requires i < height.Length
    reads height
    decreases height.Length - i
{
    if i == height.Length - 1 then height[i]
    else max(height[i], maxRight(height, i+1))
}

function waterAt(height: array<nat>, i: nat): nat
    requires i < height.Length
    reads height
{
    if height.Length <= 1 then 0
    else
        var left := maxLeft(height, i);
        var right := maxRight(height, i);
        var waterLevel := min(left, right);
        if waterLevel > height[i] then waterLevel - height[i] else 0
}
// </vc-helpers>

// <vc-spec>
method TrapRainWater(height: array<nat>) returns (result: nat)
    requires height.Length >= 0
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    if height.Length <= 1 {
        result := 0;
    } else {
        result := 0;
        var i := 0;
        while i < height.Length
            invariant 0 <= i <= height.Length
            invariant result >= 0
        {
            result := result + waterAt(height, i);
            i := i + 1;
        }
    }
}
// </vc-code>
