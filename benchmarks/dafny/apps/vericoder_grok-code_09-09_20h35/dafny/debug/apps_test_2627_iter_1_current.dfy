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
method HistogramMaxArea(heights: seq<int>) returns (area: int)
    requires |heights| > 0
    requires forall i :: 0 <= i < |heights| ==> heights[i] >= 0
    ensures area >= 0
{
    area := 0;
    var stack: seq<int> := [];
    var i: int := 0;
    while i <= |heights|
    {
        var h := if i < |heights| then heights[i] else -1;
        while |stack| > 0 && heights[stack[|stack|-1]] >= h
        {
            var top := stack[|stack|-1];
            stack := stack[..|stack|-1];
            var start := if |stack| == 0 then -1 else stack[|stack|-1];
            var width := i - start - 1;
            var currArea := width * heights[top];
            if currArea > area {
                area := currArea;
            }
        }
        if i < |heights| {
            stack := stack + [i];
        }
        i := i + 1;
    }
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
        result := 0;
    } else {
        result := 0;
        var heights: seq<int> := seq<int>(|matrix[0]|, i => 0);
        var row: int := 0;
        while row < |matrix|
        {
            var newHeights: seq<int> := heights;
            var j: int := 0;
            while j < |matrix[0]|
            {
                if matrix[row][j] == "1" {
                    newHeights := newHeights[j := newHeights[j] + 1];
                } else {
                    newHeights := newHeights[j := 0];
                }
                j := j + 1;
            }
            heights := newHeights;
            var currentArea: int := HistogramMaxArea(heights);
            if currentArea > result {
                result := currentArea;
            }
            row := row + 1;
        }
    }
}
// </vc-code>

