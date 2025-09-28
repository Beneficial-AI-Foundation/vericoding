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
/* helper modified by LLM (iteration 5): new lemma for sequence properties */
lemma Lemma_Concat_Split_1<T>(s1: seq<T>, s2: seq<T>)
    requires |s1| >= 1
    ensures s1[1..] + s2 == (s1+s2)[1..]
{
}

/* helper modified by LLM (iteration 5): fixed proof of SumSeqConcat using a helper lemma */
lemma SumSeqConcat(s1: seq<real>, s2: seq<real>)
  ensures SumSeq(s1 + s2) == SumSeq(s1) + SumSeq(s2)
  decreases |s1|
{
  if |s1| > 0 {
    SumSeqConcat(s1[1..], s2);
    Lemma_Concat_Split_1(s1, s2);
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
  /* code modified by LLM (iteration 5): added assert to help prove invariant */
  var n := |matrix|;
  result := 0.0;
  var i := 0;
  ghost var diag := GetDiagonal(matrix, n);
  assert diag == GetDiagonal(matrix, n);
  while i < n
    invariant 0 <= i <= n
    invariant diag == GetDiagonal(matrix, n)
    invariant result == SumSeq(diag[..i])
  {
    SumSeqConcat(diag[..i], [diag[i]]);
    assert SumSeq([diag[i]]) == diag[i];
    result := result + matrix[i][i];
    i := i + 1;
    assert result == SumSeq(diag[..i]);
  }
}
// </vc-code>
