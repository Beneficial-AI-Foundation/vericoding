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
// No helper lemmas needed for this solution.
// </vc-helpers>

// <vc-spec>
method generate(numRows: int) returns (result: seq<seq<int>>)
  requires numRows >= 0
  ensures ValidPascalTriangle(result, numRows)
// </vc-spec>
// <vc-code>
{
  var triangle: seq<seq<int>> := [];
  var i := 0;
  while i < numRows
    invariant 0 <= i <= numRows
    invariant |triangle| == i
    invariant ValidPascalTriangle(triangle, i)
    decreases numRows - i
  {
    if i == 0 {
      triangle := triangle + [[1]];
    } else {
      var prev := triangle[i-1];
      var r: seq<int> := [1];
      var j := 1;
      while j < i
        invariant 1 <= j <= i
        invariant |r| == j
        invariant r[0] == 1
        invariant forall k :: 1 <= k < |r| ==> r[k] == prev[k-1] + prev[k]
        decreases i - j
      {
        r := r + [prev[j-1] + prev[j]];
        j := j + 1;
      }
      r := r + [1];
      // Now r has length i+1 and satisfies the Pascal properties for row i
      triangle := triangle + [r];
    }
    i := i + 1;
  }
  result := triangle;
}
// </vc-code>

