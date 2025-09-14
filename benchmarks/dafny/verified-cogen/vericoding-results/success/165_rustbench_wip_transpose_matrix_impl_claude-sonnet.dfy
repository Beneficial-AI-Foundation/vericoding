// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Transpose(matrix: seq<seq<int>>) returns (result: seq<seq<int>>)
    requires |matrix| > 0
    requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
    requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix|
    ensures |result| == |matrix[0]|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |matrix|
    ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==> result[i][j] == matrix[j][i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added bounds checking to prevent index out of range errors */
    var rows := |matrix|;
    var cols := |matrix[0]|;
    
    result := seq(cols, i requires 0 <= i < cols => seq(rows, j requires 0 <= j < rows => matrix[j][i]));
}
// </vc-code>
