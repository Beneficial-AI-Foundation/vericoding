// <vc-preamble>
// Helper predicate to check if a matrix has valid dimensions
predicate IsValidMatrix(m: seq<seq<real>>, rows: nat, cols: nat)
{
    |m| == rows && forall i :: 0 <= i < |m| ==> |m[i]| == cols
}
// </vc-preamble>

// <vc-helpers>
function ConcatRows(left: seq<real>, right: seq<real>): seq<real>
{
    left + right
}

function ConcatMatrix(top: seq<seq<real>>, bottom: seq<seq<real>>): seq<seq<real>>
{
    top + bottom
}

/* helper modified by LLM (iteration 3): added bounds checking lemmas with triggers */
lemma ConcatRowsLength(left: seq<real>, right: seq<real>)
    ensures |ConcatRows(left, right)| == |left| + |right|
{
}

lemma ConcatMatrixLength(top: seq<seq<real>>, bottom: seq<seq<real>>)
    ensures |ConcatMatrix(top, bottom)| == |top| + |bottom|
{
}

lemma TopRightBounds(topLeft: seq<seq<real>>, topRight: seq<seq<real>>)
    requires |topLeft| == |topRight|
    ensures forall i {:trigger topLeft[i]} :: 0 <= i < |topLeft| ==> 0 <= i < |topRight|
{
}

lemma BottomRightBounds(bottomLeft: seq<seq<real>>, bottomRight: seq<seq<real>>)
    requires |bottomLeft| == |bottomRight|
    ensures forall i {:trigger bottomLeft[i]} :: 0 <= i < |bottomLeft| ==> 0 <= i < |bottomRight|
{
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
    /* code modified by LLM (iteration 3): added bounds checking before sequence construction */
    TopRightBounds(topLeft, topRight);
    BottomRightBounds(bottomLeft, bottomRight);
    
    var topRows := seq(|topLeft|, i requires 0 <= i < |topLeft| => ConcatRows(topLeft[i], topRight[i]));
    var bottomRows := seq(|bottomLeft|, i requires 0 <= i < |bottomLeft| => ConcatRows(bottomLeft[i], bottomRight[i]));
    result := ConcatMatrix(topRows, bottomRows);
}
// </vc-code>
