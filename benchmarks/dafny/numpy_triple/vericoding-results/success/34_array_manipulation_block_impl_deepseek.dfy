// <vc-preamble>
// Helper predicate to check if a matrix has valid dimensions
predicate IsValidMatrix(m: seq<seq<real>>, rows: nat, cols: nat)
{
    |m| == rows && forall i :: 0 <= i < |m| ==> |m[i]| == cols
}
// </vc-preamble>

// <vc-helpers>

lemma LemmaTopLeftTopRightDimensions(topLeft: seq<seq<real>>, topRight: seq<seq<real>>)
    requires |topLeft| > 0 && |topLeft[0]| > 0
    requires |topRight| > 0 && |topRight[0]| > 0
    requires |topLeft| == |topRight|
    requires forall i :: 0 <= i < |topLeft| ==> |topLeft[i]| == |topLeft[0]|
    requires forall i :: 0 <= i < |topRight| ==> |topRight[i]| == |topRight[0]|
    ensures forall i :: 0 <= i < |topLeft| ==> |topLeft[i]| == |topLeft[0]| && |topRight[i]| == |topRight[0]|
{
}

lemma LemmaBottomLeftBottomRightDimensions(bottomLeft: seq<seq<real>>, bottomRight: seq<seq<real>>)
    requires |bottomLeft| > 0 && |bottomLeft[0]| > 0
    requires |bottomRight| > 0 && |bottomRight[0]| > 0
    requires |bottomLeft| == |bottomRight|
    requires forall i :: 0 <= i < |bottomLeft| ==> |bottomLeft[i]| == |bottomLeft[0]|
    requires forall i :: 0 <= i < |bottomRight| ==> |bottomRight[i]| == |bottomRight[0]|
    ensures forall i :: 0 <= i < |bottomLeft| ==> |bottomLeft[i]| == |bottomLeft[0]| && |bottomRight[i]| == |bottomRight[0]|
{
}

lemma LemmaMatrixConsistency(topLeft: seq<seq<real>>, topRight: seq<seq<real>>, bottomLeft: seq<seq<real>>, bottomRight: seq<seq<real>>)
    requires |topLeft| > 0 && |topLeft[0]| > 0
    requires |topRight| > 0 && |topRight[0]| > 0
    requires |bottomLeft| > 0 && |bottomLeft[0]| > 0
    requires |bottomRight| > 0 && |bottomRight[0]| > 0
    requires |topLeft| == |topRight|
    requires |bottomLeft| == |bottomRight|
    requires forall i :: 0 <= i < |topLeft| ==> |topLeft[i]| == |topLeft[0]|
    requires forall i :: 0 <= i < |bottomLeft| ==> |bottomLeft[i]| == |topLeft[0]|
    requires forall i :: 0 <= i < |topRight| ==> |topRight[i]| == |topRight[0]|
    requires forall i :: 0 <= i < |bottomRight| ==> |bottomRight[i]| == |topRight[0]|
    ensures forall i :: 0 <= i < |topLeft| ==> |topLeft[i]| == |topLeft[0]| && |topRight[i]| == |topRight[0]|
    ensures forall i :: 0 <= i < |bottomLeft| ==> |bottomLeft[i]| == |topLeft[0]| && |bottomRight[i]| == |topRight[0]|
{
    LemmaTopLeftTopRightDimensions(topLeft, topRight);
    LemmaBottomLeftBottomRightDimensions(bottomLeft, bottomRight);
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
  /* code modified by LLM (iteration 3): Added proper invariants and verification support */
  LemmaMatrixConsistency(topLeft, topRight, bottomLeft, bottomRight);
  
  var totalRows := |topLeft| + |bottomLeft|;
  var totalCols := |topLeft[0]| + |topRight[0]|;
  var res : seq<seq<real>> := [];
  
  // Process top half (topLeft + topRight)
  var i := 0;
  while i < |topLeft|
    invariant i <= |topLeft|
    invariant |res| == i
    invariant forall k :: 0 <= k < i ==> |res[k]| == totalCols
    invariant forall k, l :: 0 <= k < i && 0 <= l < |topLeft[0]| ==> res[k][l] == topLeft[k][l]
    invariant forall k, l :: 0 <= k < i && 0 <= l < |topRight[0]| ==> res[k][|topLeft[0]| + l] == topRight[k][l]
  {
    var row : seq<real> := [];
    var j := 0;
    while j < |topLeft[0]|
      invariant j <= |topLeft[0]|
      invariant |row| == j
      invariant forall k :: 0 <= k < j ==> row[k] == topLeft[i][k]
    {
      row := row + [topLeft[i][j]];
      j := j + 1;
    }
    
    j := 0;
    while j < |topRight[0]|
      invariant j <= |topRight[0]|
      invariant |row| == |topLeft[0]| + j
      invariant forall k :: 0 <= k < |topLeft[0]| ==> row[k] == topLeft[i][k]
      invariant forall k :: 0 <= k < j ==> row[|topLeft[0]| + k] == topRight[i][k]
    {
      row := row + [topRight[i][j]];
      j := j + 1;
    }
    
    res := res + [row];
    i := i + 1;
  }
  
  // Process bottom half (bottomLeft + bottomRight)
  i := 0;
  while i < |bottomLeft|
    invariant i <= |bottomLeft|
    invariant |res| == |topLeft| + i
    invariant forall k :: 0 <= k < |res| ==> |res[k]| == totalCols
    invariant forall k, l :: 0 <= k < |topLeft| && 0 <= l < |topLeft[0]| ==> res[k][l] == topLeft[k][l]
    invariant forall k, l :: 0 <= k < |topLeft| && 0 <= l < |topRight[0]| ==> res[k][|topLeft[0]| + l] == topRight[k][l]
    invariant forall k, l :: 0 <= k < i && 0 <= l < |bottomLeft[0]| ==> res[|topLeft| + k][l] == bottomLeft[k][l]
    invariant forall k, l :: 0 <= k < i && 0 <= l < |bottomRight[0]| ==> res[|topLeft| + k][|topLeft[0]| + l] == bottomRight[k][l]
  {
    var row : seq<real> := [];
    var j := 0;
    while j < |bottomLeft[0]|
      invariant j <= |bottomLeft[0]|
      invariant |row| == j
      invariant forall k :: 0 <= k < j ==> row[k] == bottomLeft[i][k]
    {
      row := row + [bottomLeft[i][j]];
      j := j + 1;
    }
    
    j := 0;
    while j < |bottomRight[0]|
      invariant j <= |bottomRight[0]|
      invariant |row| == |bottomLeft[0]| + j
      invariant forall k :: 0 <= k < |bottomLeft[0]| ==> row[k] == bottomLeft[i][k]
      invariant forall k :: 0 <= k < j ==> row[|bottomLeft[0]| + k] == bottomRight[i][k]
    {
      row := row + [bottomRight[i][j]];
      j := j + 1;
    }
    
    res := res + [row];
    i := i + 1;
  }
  
  result := res;
}
// </vc-code>
