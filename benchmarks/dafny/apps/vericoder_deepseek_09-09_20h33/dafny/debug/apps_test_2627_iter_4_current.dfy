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
function RectArea(width: int, height: int): int
  requires width >= 0 && height >= 0
  ensures RectArea(width, height) >= 0
{
  width * height
}

predicate ValidHeights(heights: seq<int>, maxHeight: int) {
  forall k :: 0 <= k < |heights| ==> 0 <= heights[k] <= maxHeight
}

predicate MonotonicStack(stack: seq<int>) {
  forall k :: 1 <= k < |stack| ==> stack[k-1] < stack[k]
}

function AllOnesRect(matrix: seq<seq<string>>, i: int, j: int, width: int, height: int): bool {
  false  // Placeholder - not used in current implementation
}

lemma LargeRectanglesImpossible(matrix: seq<seq<string>>, width: int, height: int)
  requires ValidMatrix(matrix)
  requires width > |matrix[0]| || height > |matrix|
  ensures !(exists i, j :: 0 <= i < |matrix| - height + 1 && 0 <= j < |matrix[0]| - width + 1 && 
           AllOnesRect(matrix, i, j, width, height))
{
}

ghost function MaxAreaForRow(heights: seq<int>): int
  requires |heights| >= 0
  requires forall k :: 0 <= k < |heights| ==> heights[k] >= 0
{
  if |heights| == 0 then 0 else
    var max_area := 0;
    var stack: seq<int> := [-1];
    var j := 0;
    
    while j <= |heights|
      invariant 0 <= j <= |heights|
      invariant |stack| >= 1
      invariant stack[0] == -1
      invariant MonotonicStack(stack)
      invariant max_area >= 0
    {
      while |stack| > 1 && (j == |heights| || heights[j] < heights[stack[|stack|-1]])
        invariant |stack| >= 1
        invariant MonotonicStack(stack)
      {
        var top_index := stack[|stack|-1];
        var h := heights[top_index];
        stack := stack[0..|stack|-1];
        var w := j - stack[|stack|-1] - 1;
        var area := RectArea(w, h);
        if area > max_area {
          max_area := area;
        }
      }
      if j < |heights| {
        stack := stack + [j];
      }
      j := j + 1;
    }
    max_area
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
  
  var max_area := 0;
  var heights: seq<int> := [];
  heights := seq(m, i => 0);
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |heights| == m
    invariant ValidHeights(heights, i)
  {
    var j := 0;
    while j < m
      invariant 0 <= j <= m
      invariant |heights| == m
      invariant ValidHeights(heights, i+1)
    {
      if matrix[i][j] == "1" {
        heights := heights[j := heights[j] + 1];
      } else {
        heights := heights[j := 0];
      }
      j := j + 1;
    }
    
    var stack: seq<int> := [-1];
    j := 0;
    while j <= m
      invariant 0 <= j <= m
      invariant |stack| >= 1
      invariant stack[0] == -1
      invariant MonotonicStack(stack)
      invariant max_area >= 0
    {
      while |stack| > 1 && (j == m || heights[j] < heights[stack[|stack|-1]])
        invariant |stack| >= 1
        invariant MonotonicStack(stack)
      {
        var top_index := stack[|stack|-1];
        var height_val := heights[top_index];
        stack := stack[0..|stack|-1];
        var width := j - stack[|stack|-1] - 1;
        var area := RectArea(width, height_val);
        if area > max_area {
          max_area := area;
        }
      }
      if j < m {
        stack := stack + [j];
      }
      j := j + 1;
    }
    
    i := i + 1;
  }
  
  return max_area;
}
// </vc-code>

