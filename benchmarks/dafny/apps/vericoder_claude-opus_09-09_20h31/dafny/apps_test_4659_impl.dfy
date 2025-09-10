predicate ValidPascalTriangle(triangle: seq<seq<int>>, numRows: int)
{
  |triangle| == numRows &&
  (numRows == 0 ==> triangle == []) &&
  (numRows > 0 ==> (
    forall i :: 0 <= i < |triangle| ==> |triangle[i]| == i + 1
  )) &&
  (numRows > 0 ==> (
    forall i :: 0 <= i < |triangle| ==> triangle[i][0] == 1 && triangle[i][|triangle[i]| - 1] == 1
  )) &&
  (numRows > 1 ==> (
    forall i :: 1 <= i < |triangle| ==> 
      forall j :: 1 <= j < |triangle[i]| - 1 ==> 
        triangle[i][j] == triangle[i-1][j-1] + triangle[i-1][j]
  ))
}

// <vc-helpers>
lemma ValidPascalTriangleExtension(triangle: seq<seq<int>>, numRows: int)
  requires numRows > 0
  requires ValidPascalTriangle(triangle, numRows)
  ensures forall i :: 0 <= i < numRows ==> |triangle[i]| == i + 1
  ensures forall i :: 0 <= i < numRows ==> triangle[i][0] == 1 && triangle[i][|triangle[i]| - 1] == 1
  ensures numRows > 1 ==> forall i :: 1 <= i < numRows ==> 
    forall j :: 1 <= j < |triangle[i]| - 1 ==> 
      triangle[i][j] == triangle[i-1][j-1] + triangle[i-1][j]
{
  // This lemma helps Dafny understand the properties are maintained
}
// </vc-helpers>

// <vc-spec>
method generate(numRows: int) returns (result: seq<seq<int>>)
  requires numRows >= 0
  ensures ValidPascalTriangle(result, numRows)
// </vc-spec>
// <vc-code>
{
  if numRows == 0 {
    return [];
  }
  
  var triangle: seq<seq<int>> := [[1]];
  var i := 1;
  
  while i < numRows
    invariant 1 <= i <= numRows
    invariant ValidPascalTriangle(triangle, i)
  {
    var prevRow := triangle[i-1];
    var newRow: seq<int> := [1];
    var j := 1;
    
    while j < i
      invariant 1 <= j <= i
      invariant |newRow| == j
      invariant newRow[0] == 1
      invariant forall k :: 1 <= k < j ==> newRow[k] == prevRow[k-1] + prevRow[k]
    {
      newRow := newRow + [prevRow[j-1] + prevRow[j]];
      j := j + 1;
    }
    
    newRow := newRow + [1];
    triangle := triangle + [newRow];
    i := i + 1;
  }
  
  return triangle;
}
// </vc-code>

