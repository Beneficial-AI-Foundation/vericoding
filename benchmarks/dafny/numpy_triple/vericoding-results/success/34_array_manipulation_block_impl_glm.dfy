// <vc-preamble>
// Helper predicate to check if a matrix has valid dimensions
predicate IsValidMatrix(m: seq<seq<real>>, rows: nat, cols: nat)
{
    |m| == rows && forall i :: 0 <= i < |m| ==> |m[i]| == cols
}
// </vc-preamble>

// <vc-helpers>
function ConcatenateRows(row1: seq<real>, row2: seq<real>): seq<real> {
  row1 + row2
}
// </vc-helpers>

// <vc-spec>
method Block(topLeft: seq<seq<real>>, topRight: seq<seq<real>>, 
             bottomLeft: seq<seq<real>>, bottomRight: seq<seq<real>>)
    returns (result: seq<seq<real>>)
    requires |topLeft| > 0 && |topLeft[0]| > 0
    requires |topRight| > 0 && |topRight[0]| > 0
    requires |bottomLeft| > 0 && |bottomLeft[0]| > 0
    requires |bottomRight| > 0 && |bottomRight[0]| > 0
    // All matrices in top row must have same number of rows
    requires |topLeft| == |topRight|
    // All matrices in bottom row must have same number of rows
    requires |bottomLeft| == |bottomRight|
    // All matrices in left column must have same number of columns
    requires forall i :: 0 <= i < |topLeft| ==> |topLeft[i]| == |topLeft[0]|
    requires forall i :: 0 <= i < |bottomLeft| ==> |bottomLeft[i]| == |topLeft[0]|
    // All matrices in right column must have same number of columns
    requires forall i :: 0 <= i < |topRight| ==> |topRight[i]| == |topRight[0]|
    requires forall i :: 0 <= i < |bottomRight| ==> |bottomRight[i]| == |topRight[0]|
    // Input matrices must be well-formed
    requires IsValidMatrix(topLeft, |topLeft|, |topLeft[0]|)
    requires IsValidMatrix(topRight, |topRight|, |topRight[0]|)
    requires IsValidMatrix(bottomLeft, |bottomLeft|, |bottomLeft[0]|)
    requires IsValidMatrix(bottomRight, |bottomRight|, |bottomRight[0]|)
    
    ensures |result| == |topLeft| + |bottomLeft|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |topLeft[0]| + |topRight[0]|
    ensures IsValidMatrix(result, |topLeft| + |bottomLeft|, |topLeft[0]| + |topRight[0]|)
    
    // Top-left block elements are correctly placed
    ensures forall i, j :: 0 <= i < |topLeft| && 0 <= j < |topLeft[0]| ==>
        result[i][j] == topLeft[i][j]
    
    // Top-right block elements are correctly placed
    ensures forall i, j :: 0 <= i < |topRight| && 0 <= j < |topRight[0]| ==>
        result[i][|topLeft[0]| + j] == topRight[i][j]
    
    // Bottom-left block elements are correctly placed
    ensures forall i, j :: 0 <= i < |bottomLeft| && 0 <= j < |bottomLeft[0]| ==>
        result[|topLeft| + i][j] == bottomLeft[i][j]
    
    // Bottom-right block elements are correctly placed
    ensures forall i, j :: 0 <= i < |bottomRight| && 0 <= j < |bottomRight[0]| ==>
        result[|topLeft| + i][|topLeft[0]| + j] == bottomRight[i][j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): build result by concatenating rows immutably */
  var topRows := |topLeft|;
  var bottomRows := |bottomLeft|;
  
  // Build top part: rows from topLeft and topRight
  var topPart: seq<seq<real>> := [];
  for i := 0 to topRows
    invariant 0 <= i <= topRows
    invariant |topPart| == i
    invariant forall j :: 0 <= j < i ==> topPart[j] == ConcatenateRows(topLeft[j], topRight[j])
  {
    var newRow := ConcatenateRows(topLeft[i], topRight[i]);
    topPart := topPart + [newRow];
  }
  
  // Build bottom part: rows from bottomLeft and bottomRight
  var bottomPart: seq<seq<real>> := [];
  for i := 0 to bottomRows
    invariant 0 <= i <= bottomRows
    invariant |bottomPart| == i
    invariant forall j :: 0 <= j < i ==> bottomPart[j] == ConcatenateRows(bottomLeft[j], bottomRight[j])
  {
    var newRow := ConcatenateRows(bottomLeft[i], bottomRight[i]);
    bottomPart := bottomPart + [newRow];
  }
  
  result := topPart + bottomPart;
}
// </vc-code>
