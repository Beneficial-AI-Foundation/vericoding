// <vc-preamble>
// Helper function to compute sum of a sequence of reals
ghost function SumSeq(s: seq<real>): real
{
    if |s| == 0 then 0.0 else s[0] + SumSeq(s[1..])
}

// Helper function to extract diagonal elements from a square matrix
ghost function GetDiagonal(matrix: seq<seq<real>>, n: nat): seq<real>
    requires n >= 0
    requires |matrix| == n
    requires forall i :: 0 <= i < n ==> |matrix[i]| == n
{
    seq(n, i requires 0 <= i < n => matrix[i][i])
}

// Method to compute the trace of a square matrix
// </vc-preamble>

// <vc-helpers>
/* helpers modified by LLM (iteration 5): Remove duplicate function declarations and keep non-ghost versions */
function SumSeq(s: seq<real>): real
{
    if |s| == 0 then 0.0 else s[0] + SumSeq(s[1..])
}

function GetDiagonal(matrix: seq<seq<real>>, n: nat): seq<real>
    requires n >= 0
    requires |matrix| == n
    requires forall i :: 0 <= i < n ==> |matrix[i]| == n
{
    seq(n, i requires 0 <= i < n => matrix[i][i])
}

lemma DiagonalExtraction(matrix: seq<seq<real>>, n: nat)
  requires n >= 0
  requires |matrix| == n
  requires forall i :: 0 <= i < n ==> |matrix[i]| == n
  ensures |GetDiagonal(matrix, n)| == n
  ensures forall i :: 0 <= i < n ==> GetDiagonal(matrix, n)[i] == matrix[i][i]
{
}

lemma SumSeqAppend(s: seq<real>, t: seq<real>)
  ensures SumSeq(s + t) == SumSeq(s) + SumSeq(t)
{
}

lemma SumSeqSingle(x: real)
  ensures SumSeq([x]) == x
{
}

lemma SumSeqEmpty()
  ensures SumSeq([]) == 0.0
{
}
// </vc-helpers>

// <vc-spec>
method Trace(matrix: seq<seq<real>>) returns (result: real)
    // The matrix must be square (including empty matrices)
    requires |matrix| >= 0
    requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix|
    
    // The result equals the sum of diagonal elements
    ensures result == SumSeq(GetDiagonal(matrix, |matrix|))
    
    // If any diagonal element is non-zero, then the result is non-zero
    ensures (exists i :: 0 <= i < |matrix| && matrix[i][i] != 0.0) ==> result != 0.0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Remove ghost keyword from variable declaration */
{
  var n := |matrix|;
  var diagonal := GetDiagonal(matrix, n);
  assert diagonal == seq(n, i requires 0 <= i < n => matrix[i][i]);
  assert |diagonal| == n;
  assert forall i :: 0 <= i < n ==> diagonal[i] == matrix[i][i];
  result := SumSeq(diagonal);
  assert result == SumSeq(GetDiagonal(matrix, n));
}
// </vc-code>
