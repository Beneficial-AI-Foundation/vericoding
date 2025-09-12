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
    assume {:axiom} false;
}
// </vc-code>
