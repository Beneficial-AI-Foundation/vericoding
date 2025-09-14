// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added decreases clause to fix termination proof */
predicate IsValidIndex(i: int, len: int) { 0 <= i < len }

function MaxLeft(heights: array<int>, i: int): int
    requires 0 <= i < heights.Length
    reads heights
    decreases i
{
    if i == 0 then heights[0]
    else if heights[i] > MaxLeft(heights, i-1) then heights[i]
    else MaxLeft(heights, i-1)
}

function MaxRight(heights: array<int>, i: int): int
    requires 0 <= i < heights.Length
    reads heights
    decreases heights.Length - i
{
    if i == heights.Length - 1 then heights[i]
    else if heights[i] > MaxRight(heights, i+1) then heights[i]
    else MaxRight(heights, i+1)
}

function WaterAtPosition(heights: array<int>, i: int): int
    requires 0 <= i < heights.Length
    reads heights
{
    var leftMax := MaxLeft(heights, i);
    var rightMax := MaxRight(heights, i);
    var waterLevel := if leftMax < rightMax then leftMax else rightMax;
    if waterLevel > heights[i] then waterLevel - heights[i] else 0
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
    /* code modified by LLM (iteration 2): unchanged implementation using fixed helpers */
    result := 0;
    if heights.Length < 3 {
        return;
    }
    
    var i := 1;
    while i < heights.Length - 1
        invariant 1 <= i <= heights.Length - 1
        invariant result >= 0
    {
        var water := WaterAtPosition(heights, i);
        result := result + water;
        i := i + 1;
    }
}
// </vc-code>
