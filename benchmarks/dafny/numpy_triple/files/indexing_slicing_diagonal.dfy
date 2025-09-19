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
  assume {:axiom} false;
}
// </vc-code>
