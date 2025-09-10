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
function sum(a: int, b: int): int { a + b }
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

    var result_var: seq<seq<int>> := [[1]]; // First row

    if numRows >= 2 {
        var prevRow: seq<int> := [1];
        for i := 1 to numRows - 1
            invariant 1 <= i <= numRows - 1
            invariant |result_var| == i
            invariant ValidPascalTriangle(result_var, i)
            invariant prevRow == result_var[i-1]
        {
            var currentRow: seq<int> := [1];
            // Ensure j loop's range is valid
            if i > 0 { 
                for j := 1 to i - 1
                    invariant 1 <= j <= i - 1
                    invariant |currentRow| == j + 1
                    invariant currentRow[0] == 1
                    invariant forall k :: 1 <= k < |currentRow|-1 ==> currentRow[k] == prevRow[k-1] + prevRow[k]
                {
                    currentRow := currentRow + [prevRow[j-1] + prevRow[j]];
                }
            }
            currentRow := currentRow + [1];
            result_var := result_var + [currentRow];
            prevRow := currentRow;
        }
    }
    return result_var;
}
// </vc-code>

