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
lemma PascalRowProperty(triangle: seq<seq<int>>, i: int)
  requires 0 <= i < |triangle|
  requires |triangle| > 0
  requires forall k :: 0 <= k < |triangle| ==> |triangle[k]| == k + 1
  requires forall k :: 0 <= k < |triangle| ==> triangle[k][0] == 1 && triangle[k][|triangle[k]| - 1] == 1
  ensures triangle[i][0] == 1 && triangle[i][|triangle[i]| - 1] == 1
{
}

lemma PascalSumProperty(triangle: seq<seq<int>>, i: int, j: int)
  requires 1 <= i < |triangle|
  requires 1 <= j < |triangle[i]| - 1
  requires forall k :: 0 <= k < |triangle| ==> |triangle[k]| == k + 1
  requires forall k :: 1 <= k < |triangle| ==> 
    forall l :: 1 <= l < |triangle[k]| - 1 ==> 
      triangle[k][l] == triangle[k-1][l-1] + triangle[k-1][l]
  ensures triangle[i][j] == triangle[i-1][j-1] + triangle[i-1][j]
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
  result := [];
  if numRows == 0 {
    return;
  }
  
  var i := 0;
  while i < numRows
    invariant 0 <= i <= numRows
    invariant |result| == i
    invariant i > 0 ==> ValidPascalTriangle(result, i)
  {
    var row := new int[i+1];
    row[0] := 1;
    row[i] := 1;
    
    if i > 0 {
      var j := 1;
      while j < i
        invariant 1 <= j <= i
        invariant forall k :: 0 <= k < j ==> row[k] == (if k == 0 || k == i then 1 else result[i-1][k-1] + result[i-1][k])
      {
        row[j] := result[i-1][j-1] + result[i-1][j];
        j := j + 1;
      }
    }
    
    result := result + [row[..]];
    i := i + 1;
  }
}
// </vc-code>

