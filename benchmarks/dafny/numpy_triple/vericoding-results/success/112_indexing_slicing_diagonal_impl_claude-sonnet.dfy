// <vc-preamble>
// Method to extract diagonal elements from a 2D matrix with optional offset


// Helper function to compute minimum of two integers
function Minimum(a: int, b: int): int
  ensures Minimum(a, b) == if a <= b then a else b
{
  if a <= b then a else b
}
// </vc-preamble>

// <vc-helpers>
// Predicate to check if a matrix is rectangular
predicate IsRectangular(matrix: seq<seq<real>>)
{
  |matrix| == 0 || (forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|)
}

/* helper modified by LLM (iteration 4): Fixed DiagonalLength to ensure non-negative results and handle edge cases */
// Function to calculate diagonal length
function DiagonalLength(rows: int, cols: int, offset: int): int
  requires rows >= 0 && cols >= 0
  ensures DiagonalLength(rows, cols, offset) >= 0
{
  if rows == 0 || cols == 0 then 0
  else if offset >= 0 then 
    var temp := cols - offset;
    if temp <= 0 then 0 else Minimum(rows, temp)
  else 
    var temp := rows + offset;
    if temp <= 0 then 0 else Minimum(cols, temp)
}
// </vc-helpers>

// <vc-spec>
method Diagonal(matrix: seq<seq<real>>, offset: int := 0) returns (result: seq<real>)
  // Precondition: Matrix must be rectangular (all rows have same length)
  requires |matrix| > 0 ==> (forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|)
  // Precondition: Matrix dimensions must accommodate the offset for meaningful results
  requires |matrix| > 0 ==> 
    if offset >= 0 then offset <= |matrix[0]| 
    else -offset <= |matrix|
  // Postcondition: Result size matches diagonal size calculation
  ensures |matrix| == 0 ==> |result| == 0
  ensures |matrix| > 0 ==> 
    |result| == (if offset >= 0 
                 then Minimum(|matrix|, |matrix[0]| - offset)
                 else Minimum(|matrix[0]|, |matrix| + offset))
  // Postcondition: Each element comes from correct diagonal position
  ensures |matrix| > 0 ==> forall i :: 0 <= i < |result| ==>
    (if offset >= 0 
     then result[i] == matrix[i][i + offset]
     else result[i] == matrix[i + (-offset)][i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Fixed bounds checking and loop invariant to handle all cases properly */
  if |matrix| == 0 {
    result := [];
    return;
  }
  
  var diag_length := if offset >= 0 
                     then Minimum(|matrix|, |matrix[0]| - offset)
                     else Minimum(|matrix[0]|, |matrix| + offset);
  
  if diag_length <= 0 {
    result := [];
    return;
  }
  
  result := [];
  var i := 0;
  
  while i < diag_length
    invariant 0 <= i <= diag_length
    invariant |result| == i
    invariant diag_length >= 0
    invariant offset >= 0 ==> (diag_length == Minimum(|matrix|, |matrix[0]| - offset) && diag_length <= |matrix| && diag_length <= |matrix[0]| - offset)
    invariant offset < 0 ==> (diag_length == Minimum(|matrix[0]|, |matrix| + offset) && diag_length <= |matrix[0]| && diag_length <= |matrix| + offset)
    invariant offset >= 0 ==> (forall j :: 0 <= j < i ==> j < |matrix| && j + offset < |matrix[0]| && result[j] == matrix[j][j + offset])
    invariant offset < 0 ==> (forall j :: 0 <= j < i ==> j + (-offset) < |matrix| && j < |matrix[0]| && result[j] == matrix[j + (-offset)][j])
  {
    if offset >= 0 {
      result := result + [matrix[i][i + offset]];
    } else {
      result := result + [matrix[i + (-offset)][i]];
    }
    i := i + 1;
  }
}
// </vc-code>
