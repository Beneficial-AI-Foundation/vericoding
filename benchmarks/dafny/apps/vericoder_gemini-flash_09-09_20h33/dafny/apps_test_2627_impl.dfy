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
function longestRowOfOnes(row: seq<string>): (longest: int)
    ensures longest >= 0
{
    var maxLen := 0;
    var currentLen := 0;
    for i := 0 to |row| - 1
        invariant 0 <= i <= |row|
        invariant maxLen >= 0
        invariant currentLen >= 0
        invariant currentLen == (count k | i - currentLen <= k < i && row[k] == "1" :: 1)
        invariant maxLen == (max k | 0 <= k < i :: (count l | k - (count m | k - (count n | k - (count p | p <= k && row[p] == "1" :: 1) <= l && l <= k && row[l] == "1" :: 1) <= m && m <= k && row[m] == "1" :: 1) <= n && n < k && row[n] == "1" :: 1)) // This invariant is complex and might not be fully accurate, but helps with proving maxLen property.
                                                  // A simpler invariant for maxLen is just to state maxLen is the maximum length of consecutive '1's seen so far.
                                                  
    {
        if row[i] == "1" {
            currentLen := currentLen + 1;
        } else {
            currentLen := 0;
        }
        if currentLen > maxLen {
            maxLen := currentLen;
        }
    }
    return maxLen;
}


function histogram(matrix: seq<seq<string>>, rowIndex: int): seq<int>
    requires 0 <= rowIndex < |matrix|
    requires ValidMatrix(matrix)
    ensures |histogram(matrix, rowIndex)| == (if |matrix| == 0 then 0 else |matrix[0]|)
    ensures forall j :: 0 <= j < |histogram(matrix, rowIndex)| ==> histogram(matrix, rowIndex)[j] >= 0
    ensures forall j :: 0 <= j < |histogram(matrix, rowIndex)| ==>
        histogram(matrix, rowIndex)[j] == (
            (var countLocal := 0;
            var k := rowIndex;
            while k >= 0 && matrix[k][j] == "1"
                invariant -1 <= k <= rowIndex
                invariant countLocal == (count p: int | k < p <= rowIndex && matrix[p][j] == "1" :: 1)
            {
                countLocal := countLocal + 1;
                k := k - 1;
            }
            countLocal)
        )
{
    var numCols := |matrix[0]|;

    var hist := new int[numCols];

    for j := 0 to numCols - 1
        invariant 0 <= j <= numCols
        invariant forall k_idx :: 0 <= k_idx < j ==> hist[k_idx] >= 0
        invariant forall k_idx :: 0 <= k_idx < j ==> hist[k_idx] == (
            (var countLocal_inner := 0;
            var l := rowIndex;
            while l >= 0 && matrix[l][k_idx] == "1"
                invariant -1 <= l <= rowIndex
                invariant countLocal_inner == (count p: int | l < p <= rowIndex && matrix[p][k_idx] == "1" :: 1)
            {
                countLocal_inner := countLocal_inner + 1;
                l := l - 1;
            }
            countLocal_inner)
        )
    {
        var count := 0;
        for i := rowIndex downto 0
            invariant -1 <= i <= rowIndex
            invariant count == (count p: int | i < p <= rowIndex && matrix[p][j] == "1" :: 1)
        {
            if matrix[i][j] == "1" {
                count := count + 1;
            } else {
                break;
            }
        }
        hist[j] := count;
    }
    return hist.seq;
}
function largestRectangleInHistogram(heights: seq<int>): (area: int)
    ensures area >= 0
{
    if |heights| == 0 then return 0;

    var stack: seq<int> := [];
    var maxArea := 0;
    var i := 0;

    while i < |heights| || |stack| > 0
        invariant 0 <= i <= |heights| + 1 // i can go up to heights.length
        invariant maxArea >= 0
        invariant forall k :: k in stack ==> 0 <= k <Heights.length // Fix: k should be an index within heights
        invariant forall k :: k in stack ==> k < i // Ensure elements in stack are processed indices
        invariant forall j, k :: j in stack && k in stack && j < k ==> heights[j] <= heights[k] // Corrected invariant for stack monotonically increasing heights
        invariant forall k :: k in stack ==> (forall l :: k < l < i && l !in stack ==> heights[l] < heights[k]) // To ensure stack stores indices in increasing order of height
    {
        if i < |heights| && (|stack| == 0 || heights[i] >= heights[stack[|stack|-1]]) {
            stack := stack + [i];
            i := i + 1;
        } else {
            if |stack| == 0 && i >= |heights| { // No more elements to process and stack is empty, break.
                break;
            }
            var top := stack[|stack|-1];
            stack := stack[..|stack|-1];
            var width := if |stack| == 0 then i else i - stack[|stack|-1] - 1;
            var currentArea := heights[top] * width;
            if currentArea > maxArea {
                maxArea := currentArea;
            }
        }
    }
    return maxArea;
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
    if EmptyMatrix(matrix) then
        return 0;

    var maxRectArea := 0;
    var numRows := |matrix;

    for i := 0 to numRows - 1
        invariant 0 <= i <= numRows
        invariant maxRectArea >= 0
        invariant ValidMatrix(matrix)
        invariant forall k :: 0 <= k < i ==> maxRectArea >= largestRectangleInHistogram(histogram(matrix, k))
        // The strongest postcondition ensures that maxRectArea correctly holds the maximum area found so far.
        invariant maxRectArea == (max k | 0 <= k < i :: largestRectangleInHistogram(histogram(matrix, k)))
    {
        var currentHist := histogram(matrix, i);
        var currentArea := largestRectangleInHistogram(currentHist);
        if currentArea > maxRectArea {
            maxRectArea := currentArea;
        }
    }
    return maxRectArea;
}
// </vc-code>

