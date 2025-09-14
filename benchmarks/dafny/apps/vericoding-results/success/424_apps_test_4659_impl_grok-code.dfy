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
// No changes needed
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
  } else {
    result := [];
    var i := 0;
    while i < numRows
      invariant 0 <= i <= numRows
      invariant |result| == i
      invariant forall k :: 0 <= k < i ==> |result[k]| == k + 1
      invariant forall k :: 0 <= k < i ==> result[k][0] == 1 && result[k][|result[k]| - 1] == 1
      invariant forall k :: 1 <= k < i ==> forall j :: 1 <= j < |result[k]| - 1 ==> result[k][j] == result[k-1][j-1] + result[k-1][j]
    {
      i := i + 1;
      var row: seq<int>;
      if i == 1 {
        row := [1];
      } else {
        var prev := result[i - 2];
        row := [1];
        var j := 1;
        while j < i - 1
          invariant 1 <= j <= i - 1
          invariant |row| == j
          invariant row[0] == 1
          invariant forall m :: 1 <= m < j ==> row[m] == prev[m-1] + prev[m]
        {
          row := row + [prev[j-1] + prev[j]];
          j := j + 1;
        }
        row := row + [1];
      }
      // Assertions to help the verifier establish the outer loop invariant
      assert |row| == i;
      assert row[0] == 1;
      assert |row| > 0;
      assert row[|row|-1] == 1;
      result := result + [row];
    }
  }
}
// </vc-code>

