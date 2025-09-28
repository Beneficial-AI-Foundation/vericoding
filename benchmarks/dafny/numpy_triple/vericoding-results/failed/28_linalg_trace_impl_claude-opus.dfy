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
/* helper modified by LLM (iteration 5): Added lemma to prove loop invariant maintenance */
lemma SumSeqAppend(s: seq<real>, x: real)
    ensures SumSeq(s + [x]) == SumSeq(s) + x
{
    if |s| == 0 {
        assert s + [x] == [x];
        assert SumSeq([x]) == x;
    } else {
        assert (s + [x])[0] == s[0];
        assert (s + [x])[1..] == s[1..] + [x];
    }
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
{
  /* code modified by LLM (iteration 5): Fixed loop invariant with proper diagonal subsequence relation */
  var n := |matrix|;
  result := 0.0;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant result == SumSeq(seq(i, j requires 0 <= j < i => matrix[j][j]))
    invariant seq(i, j requires 0 <= j < i => matrix[j][j]) == GetDiagonal(matrix, n)[..i]
  {
    result := result + matrix[i][i];
    assert seq(i+1, j requires 0 <= j < i+1 => matrix[j][j]) == seq(i, j requires 0 <= j < i => matrix[j][j]) + [matrix[i][i]];
    SumSeqAppend(seq(i, j requires 0 <= j < i => matrix[j][j]), matrix[i][i]);
    i := i + 1;
  }
  
  assert seq(n, j requires 0 <= j < n => matrix[j][j]) == GetDiagonal(matrix, n);
}
// </vc-code>
