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
function method RectArea(width: int, height: int): int
  ensures RectArea(width, height) >= 0
{
  width * height
}

lemma LargeRectanglesImpossible(matrix: seq<seq<string>>, width: int, height: int)
  requires ValidMatrix(matrix)
  requires width > |matrix[0]| || height > |matrix|
  ensures !(exists i, j :: 0 <= i < |matrix| - height + 1 && 0 <= j < |matrix[0]| - width + 1 && 
           AllOnesRect(matrix, i, j, width, height))
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
  var n := |matrix|;
  if n == 0 {
    return 0;
  }
  var m := |matrix[0]|;
  
  // Maximum area found so far
  var max_area := 0;
  
  // For each starting row, calculate heights of consecutive 1's in each column
  var heights: seq<int> := [];
  heights := seq(m, i => 0);
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |heights| == m
    invariant ValidHeights(heights, n)
  {
    var j := 0;
    while j < m
      invariant 0 <= j <= m
      invariant |heights| == m
    {
      if matrix[i][j] == "1" {
        heights := heights[j := heights[j] + 1];
      } else {
        heights := heights[j := 0];
      }
      j := j + 1;
    }
    
    // Calculate max rectangle ending at this row using monotonic stack
    var stack: seq<int> := [-1];
    j := 0;
    while j <= m
      invariant 0 <= j <= m
      invariant |stack| >= 1
      invariant stack[0] == -1
      invariant MonotonicStack(stack)
    {
      while |stack| > 1 && heights[j] <= heights[stack[|stack|-1]]
        invariant |stack| >= 1
      {
        var height := heights[stack[|stack|-1]];
        stack := stack[0..|stack|-1];
        var width := j - stack[|stack|-1] - 1;
        var area := RectArea(width, height);
        if area > max_area {
          max_area := area;
        }
      }
      stack := stack + [j];
      j := j + 1;
    }
    
    i := i + 1;
  }
  
  return max_area;
}
// </vc-code>

