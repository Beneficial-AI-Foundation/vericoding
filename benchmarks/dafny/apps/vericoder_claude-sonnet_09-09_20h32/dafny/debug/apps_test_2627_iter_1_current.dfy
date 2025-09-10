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
function LargestRectangleInHistogram(heights: seq<int>): int
{
    if |heights| == 0 then 0
    else MaxAreaHelper(heights, 0, |heights| - 1)
}

function MaxAreaHelper(heights: seq<int>, left: int, right: int): int
    requires 0 <= left <= right < |heights|
{
    if left == right then
        if heights[left] >= 0 then heights[left] else 0
    else
        var mid := (left + right) / 2;
        var leftMax := MaxAreaHelper(heights, left, mid);
        var rightMax := MaxAreaHelper(heights, mid + 1, right);
        var crossMax := CrossingArea(heights, left, mid, right);
        Max3(leftMax, rightMax, crossMax)
}

function CrossingArea(heights: seq<int>, left: int, mid: int, right: int): int
    requires 0 <= left <= mid < right < |heights|
{
    var minHeight := MinInRange(heights, left, right);
    if minHeight >= 0 then minHeight * (right - left + 1) else 0
}

function MinInRange(heights: seq<int>, left: int, right: int): int
    requires 0 <= left <= right < |heights|
{
    if left == right then heights[left]
    else
        var mid := (left + right) / 2;
        var leftMin := MinInRange(heights, left, mid);
        var rightMin := MinInRange(heights, mid + 1, right);
        Min(leftMin, rightMin)
}

function Min(a: int, b: int): int
{
    if a <= b then a else b
}

function Max3(a: int, b: int, c: int): int
{
    if a >= b && a >= c then a
    else if b >= c then b
    else c
}

function ComputeHeights(matrix: seq<seq<string>>, row: int): seq<int>
    requires ValidMatrix(matrix)
    requires 0 <= row < |matrix|
{
    if EmptyMatrix(matrix) then []
    else
        seq(|matrix[0]|, j requires 0 <= j < |matrix[0]| => HeightAt(matrix, row, j))
}

function HeightAt(matrix: seq<seq<string>>, row: int, col: int): int
    requires ValidMatrix(matrix)
    requires 0 <= row < |matrix|
    requires !EmptyMatrix(matrix) && 0 <= col < |matrix[0]|
{
    if matrix[row][col] == "0" then 0
    else 1 + (if row == 0 then 0 else HeightAt(matrix, row - 1, col))
}

function MaxAreaInMatrix(matrix: seq<seq<string>>): int
    requires ValidMatrix(matrix)
{
    if EmptyMatrix(matrix) then 0
    else MaxAreaHelper2(matrix, 0)
}

function MaxAreaHelper2(matrix: seq<seq<string>>, row: int): int
    requires ValidMatrix(matrix)
    requires 0 <= row <= |matrix|
{
    if row == |matrix| then 0
    else
        var heights := ComputeHeights(matrix, row);
        var currentMax := LargestRectangleInHistogram(heights);
        var restMax := MaxAreaHelper2(matrix, row + 1);
        if currentMax >= restMax then currentMax else restMax
}

lemma MaxAreaBound(matrix: seq<seq<string>>)
    requires ValidMatrix(matrix)
    ensures MaxAreaInMatrix(matrix) <= MaxPossibleArea(matrix)
{
}

lemma MaxAreaNonNegative(matrix: seq<seq<string>>)
    requires ValidMatrix(matrix)
    ensures MaxAreaInMatrix(matrix) >= 0
{
}

lemma EmptyMatrixMaxArea(matrix: seq<seq<string>>)
    requires ValidMatrix(matrix)
    requires EmptyMatrix(matrix)
    ensures MaxAreaInMatrix(matrix) == 0
{
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
    if EmptyMatrix(matrix) {
        result := 0;
    } else {
        result := MaxAreaInMatrix(matrix);
    }
    
    MaxAreaNonNegative(matrix);
    MaxAreaBound(matrix);
    if EmptyMatrix(matrix) {
        EmptyMatrixMaxArea(matrix);
    }
}
// </vc-code>

