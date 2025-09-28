// <vc-preamble>
// Helper predicate to check if a matrix has valid dimensions
predicate IsValidMatrix(m: seq<seq<real>>, rows: nat, cols: nat)
{
    |m| == rows && forall i :: 0 <= i < |m| ==> |m[i]| == cols
}
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 3): [Added detailed loop invariants to prove postconditions.] */
  var topPart: seq<seq<real>> := [];
  var i := 0;
  while i < |topLeft|
    invariant 0 <= i <= |topLeft|
    invariant |topPart| == i
    invariant forall k :: 0 <= k < i ==> topPart[k] == topLeft[k] + topRight[k]
    invariant forall k :: 0 <= k < i ==> |topPart[k]| == |topLeft[0]| + |topRight[0]|
    invariant forall k, j :: 0 <= k < i && 0 <= j < |topLeft[0]| ==> topPart[k][j] == topLeft[k][j]
    invariant forall k, j :: 0 <= k < i && 0 <= j < |topRight[0]| ==> topPart[k][|topLeft[0]| + j] == topRight[k][j]
  {
    topPart := topPart + [topLeft[i] + topRight[i]];
    i := i + 1;
  }

  var bottomPart: seq<seq<real>> := [];
  i := 0;
  while i < |bottomLeft|
    invariant 0 <= i <= |bottomLeft|
    invariant |bottomPart| == i
    invariant forall k :: 0 <= k < i ==> bottomPart[k] == bottomLeft[k] + bottomRight[k]
    invariant forall k :: 0 <= k < i ==> |bottomPart[k]| == |topLeft[0]| + |topRight[0]|
    invariant forall k, j :: 0 <= k < i && 0 <= j < |topLeft[0]| ==> bottomPart[k][j] == bottomLeft[k][j]
    invariant forall k, j :: 0 <= k < i && 0 <= j < |topRight[0]| ==> bottomPart[k][|topLeft[0]| + j] == bottomRight[k][j]
  {
    bottomPart := bottomPart + [bottomLeft[i] + bottomRight[i]];
    i := i + 1;
  }
  
  result := topPart + bottomPart;
}
// </vc-code>
