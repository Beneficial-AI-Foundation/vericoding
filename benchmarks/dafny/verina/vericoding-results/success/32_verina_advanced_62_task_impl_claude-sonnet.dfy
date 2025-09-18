// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function MaxWater(heights: array<int>, left: int, right: int): int
    requires 0 <= left <= right < heights.Length
    reads heights
{
    if right - left < 2 then 0
    else
        var width := right - left;
        var height := if heights[left] < heights[right] then heights[left] else heights[right];
        width * height
}

function FindMaxWaterBetween(heights: array<int>, start: int, end: int): int
    requires 0 <= start <= end < heights.Length
    reads heights
    decreases end - start
{
    if end - start < 2 then 0
    else
        var current := MaxWater(heights, start, end);
        var left_max := FindMaxWaterBetween(heights, start, end - 1);
        var right_max := FindMaxWaterBetween(heights, start + 1, end);
        if current >= left_max && current >= right_max then current
        else if left_max >= right_max then left_max
        else right_max
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
    } else {
        result := FindMaxWaterBetween(heights, 0, heights.Length - 1);
    }
}
// </vc-code>
