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
/* helper modified by LLM (iteration 5): relate GetDiagonal to elementwise sequence and sum equality */
lemma SumSeq_GetDiagonal_eq(matrix: seq<seq<real>>, n: nat)
  requires |matrix| == n
  requires forall i :: 0 <= i < n ==> |matrix[i]| == n
  ensures SumSeq(GetDiagonal(matrix,n)) == SumSeq(seq(n, i => matrix[i][i]))
{
  // Show element-wise equality of the two sequences, then sums are equal
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant forall j | 0 <= j < k :: GetDiagonal(matrix,n)[j] == matrix[j][j]
  {
    // By definition of GetDiagonal, the k-th element is matrix[k][k]
    assert GetDiagonal(matrix,n)[k] == matrix[k][k];
    k := k + 1;
  }
  assert forall j | 0 <= j < n :: GetDiagonal(matrix,n)[j] == matrix[j][j];
  assert GetDiagonal(matrix,n) == seq(n, i => matrix[i][i]);
  assert SumSeq(GetDiagonal(matrix,n)) == SumSeq(seq(n, i => matrix[i][i]));
}

/* helper modified by LLM (iteration 5): prefix-sum property for arbitrary real sequences */
lemma SumSeq_Prefix(s: seq<real>, k: nat)
  requires 0 <= k < |s|
  ensures SumSeq(s[..k+1]) == SumSeq(s[..k]) + s[k]
{
  if k == 0 {
    // s[..1] has length 1 and s[..0] is empty
    assert SumSeq(s[..1]) == (if |s[..1]| == 0 then 0.0 else (s[..1])[0] + SumSeq((s[..1])[1..]));
    // simplify to s[0]
    assert SumSeq(s[..1]) == s[0];
    assert SumSeq(s[..0]) == 0.0;
    assert SumSeq(s[..1]) == SumSeq(s[..0]) + s[0];
  } else {
    // Decompose prefix: s[..k+1] = [s[0]] + s[1..k+1]
    assert SumSeq(s[..k+1]) == s[0] + SumSeq(s[1..k+1]);
    assert SumSeq(s[..k]) == s[0] + SumSeq(s[1..k]);
    // Apply induction to the tail
    SumSeq_Prefix(s[1..], k-1);
    // From induction we have SumSeq(s[1..k+1]) == SumSeq(s[1..k]) + s[k]
    assert SumSeq(s[1..k+1]) == SumSeq(s[1..k]) + s[k];
    // Conclude the desired equality
    assert SumSeq(s[..k+1]) == SumSeq(s[..k]) + s[k];
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
  /* code modified by LLM (iteration 5): compute trace by summing diagonal elements with invariant */
  var n := |matrix|;
  var acc := 0.0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant acc == SumSeq(seq(i, j => matrix[j][j]))
  {
    acc := acc + matrix[i][i];
    i := i + 1;
  }
  // At loop exit i == n
  assert acc == SumSeq(seq(n, j => matrix[j][j]));
  SumSeq_GetDiagonal_eq(matrix, n);
  assert acc == SumSeq(GetDiagonal(matrix, n));
  result := acc;
}

// </vc-code>
