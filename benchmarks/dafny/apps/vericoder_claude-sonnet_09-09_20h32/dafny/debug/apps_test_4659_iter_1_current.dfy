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
lemma ValidPascalTriangleEmpty()
  ensures ValidPascalTriangle([], 0)
{
}

lemma ValidPascalTriangleOne()
  ensures ValidPascalTriangle([[1]], 1)
{
}

lemma ValidPascalTriangleExtend(triangle: seq<seq<int>>, numRows: int, newRow: seq<int>)
  requires ValidPascalTriangle(triangle, numRows)
  requires numRows >= 0
  requires |newRow| == numRows + 1
  requires newRow[0] == 1 && newRow[numRows] == 1
  requires numRows > 0 ==> (forall j :: 1 <= j < numRows ==> newRow[j] == triangle[numRows-1][j-1] + triangle[numRows-1][j])
  ensures ValidPascalTriangle(triangle + [newRow], numRows + 1)
{
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
    result := [];
    ValidPascalTriangleEmpty();
    return;
  }
  
  result := [[1]];
  if numRows == 1 {
    ValidPascalTriangleOne();
    return;
  }
  
  var i := 1;
  while i < numRows
    invariant 1 <= i <= numRows
    invariant ValidPascalTriangle(result, i)
    invariant |result| == i
  {
    var newRow := new int[i + 1];
    newRow[0] := 1;
    newRow[i] := 1;
    
    var j := 1;
    while j < i
      invariant 1 <= j <= i
      invariant newRow[0] == 1 && newRow[i] == 1
      invariant forall k :: 1 <= k < j ==> newRow[k] == result[i-1][k-1] + result[i-1][k]
    {
      newRow[j] := result[i-1][j-1] + result[i-1][j];
      j := j + 1;
    }
    
    var newRowSeq := newRow[..];
    ValidPascalTriangleExtend(result, i, newRowSeq);
    result := result + [newRowSeq];
    i := i + 1;
  }
}
// </vc-code>

