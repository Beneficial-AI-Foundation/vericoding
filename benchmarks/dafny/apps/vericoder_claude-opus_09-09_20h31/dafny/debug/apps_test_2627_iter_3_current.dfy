predicate ValidMatrix(matrix: seq<seq<string>>)
{
    (forall i :: 0 <= i < |matrix| ==> |matrix[i]| == (if |matrix| == 0 then 0 else |matrix[0]|)) &&
    (forall i, j :: 0 <= i < |matrix| && 0 <= j < |matrix[i]| ==> matrix[i][j] == "0" || matrix[i][j] == "1")
}

function MaxPossibleArea(matrix: seq<seq<string>>): int
{
    |matrix| * (if |matrix| == 0 then 0 else |matrix[0]|)
}

predicate EmptyMatrix(matrix: seq<seq<string>>)
{
    |matrix| == 0 || |matrix[0]| == 0
}

// <vc-helpers>
function ParseInt(s: string): int
{
    if s == "0" then 0 else 1
}

method largestRectangleInHistogram(heights: seq<int>) returns (maxArea: int)
    requires forall i :: 0 <= i < |heights| ==> heights[i] >= 0
    ensures maxArea >= 0
    ensures maxArea <= |heights| * (if |heights| == 0 then 0 else MaxSeq(heights))
{
    maxArea := 0;
    for i := 0 to |heights|
        invariant 0 <= i <= |heights|
        invariant maxArea >= 0
        invariant maxArea <= |heights| * (if |heights| == 0 then 0 else MaxSeq(heights))
    {
        var minHeight := if i < |heights| then heights[i] else 0;
        for j := i to |heights|
            invariant i <= j <= |heights|
            invariant maxArea >= 0
            invariant maxArea <= |heights| * (if |heights| == 0 then 0 else MaxSeq(heights))
            invariant i < |heights| ==> (j > i ==> minHeight <= heights[i])
            invariant i < |heights| ==> (forall k :: i <= k < j && k < |heights| ==> minHeight <= heights[k])
        {
            if j > i && j < |heights| {
                minHeight := if heights[j] < minHeight then heights[j] else minHeight;
            }
            if j > i {
                var area := minHeight * (j - i);
                if area > maxArea {
                    maxArea := area;
                }
            }
        }
    }
}

function MaxSeq(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else 
        var tailMax := MaxSeq(s[1..]);
        if s[0] > tailMax then s[0] else tailMax
}
// </vc-helpers>

// <vc-spec>
method maximalRectangle(matrix: seq<seq<string>>) returns (result: int)
    requires ValidMatrix(matrix)
    ensures result >= 0
    ensures EmptyMatrix(matrix) ==> result == 0
    ensures result <= MaxPossibleArea(matrix)
// </vc-spec>
// <vc-code>
{
    if |matrix| == 0 || |matrix[0]| == 0 {
        return 0;
    }
    
    var rows := |matrix|;
    var cols := |matrix[0]|;
    var heights := seq(cols, _ => 0);
    result := 0;
    
    for i := 0 to rows
        invariant 0 <= i <= rows
        invariant |heights| == cols
        invariant forall j :: 0 <= j < cols ==> heights[j] >= 0
        invariant result >= 0
        invariant result <= rows * cols
    {
        var oldHeights := heights;
        for j := 0 to cols
            invariant 0 <= j <= cols
            invariant |heights| == cols
            invariant forall k :: 0 <= k < cols ==> heights[k] >= 0
            invariant forall k :: 0 <= k < j ==> 
                heights[k] == if matrix[i][k] == "0" then 0 else oldHeights[k] + 1
            invariant forall k :: j <= k < cols ==> heights[k] == oldHeights[k]
        {
            if matrix[i][j] == "0" {
                heights := heights[j := 0];
            } else {
                heights := heights[j := heights[j] + 1];
            }
        }
        
        var area := largestRectangleInHistogram(heights);
        if area > result {
            result := area;
        }
    }
}
// </vc-code>

