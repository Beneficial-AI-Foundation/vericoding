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
/* helper modified by LLM (iteration 5): Fixed SumSliceExtension to work properly with index ranges and corrected NonZeroPreservation logic */
lemma SumSliceExtension(s: seq<real>, i: nat)
    requires 0 <= i < |s|
    ensures SumSeq(s[0..i+1]) == SumSeq(s[0..i]) + s[i]
{
    if i == 0 {
        assert s[0..1] == [s[0]];
        assert s[0..0] == [];
        assert SumSeq([s[0]]) == s[0] + SumSeq([]);
        assert SumSeq([]) == 0.0;
    } else {
        assert s[0..i+1] == [s[0]] + s[1..i+1];
        assert s[0..i] == [s[0]] + s[1..i];
        assert SumSeq(s[0..i+1]) == s[0] + SumSeq(s[1..i+1]);
        assert SumSeq(s[0..i]) == s[0] + SumSeq(s[1..i]);
        SumSliceExtension(s[1..], i-1);
        assert SumSeq(s[1..i+1]) == SumSeq(s[1..i]) + s[i];
    }
}

lemma NonZeroPreservation(s: seq<real>, nonZeroIndex: nat)
    requires 0 <= nonZeroIndex < |s|
    requires s[nonZeroIndex] != 0.0
    ensures SumSeq(s) != 0.0
{
    if |s| == 1 {
        assert s == [s[0]];
        assert SumSeq(s) == s[0];
    } else if nonZeroIndex == 0 {
        assert SumSeq(s) == s[0] + SumSeq(s[1..]);
        assert s[0] != 0.0;
    } else {
        assert SumSeq(s) == s[0] + SumSeq(s[1..]);
        NonZeroPreservation(s[1..], nonZeroIndex - 1);
        assert SumSeq(s[1..]) != 0.0;
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
  /* code modified by LLM (iteration 5): Simplified implementation using correct slice indexing and proper postcondition handling */
  var n := |matrix|;
  result := 0.0;
  var i := 0;
  var diagonal := GetDiagonal(matrix, n);
  
  while i < n
    invariant 0 <= i <= n
    invariant result == SumSeq(diagonal[0..i])
  {
    SumSliceExtension(diagonal, i);
    result := result + matrix[i][i];
    i := i + 1;
  }
  
  assert i == n;
  assert diagonal[0..n] == diagonal;
  assert result == SumSeq(diagonal);
  
  if exists k :: 0 <= k < |matrix| && matrix[k][k] != 0.0 {
    var k :| 0 <= k < |matrix| && matrix[k][k] != 0.0;
    assert diagonal[k] == matrix[k][k];
    assert diagonal[k] != 0.0;
    NonZeroPreservation(diagonal, k);
  }
}
// </vc-code>
