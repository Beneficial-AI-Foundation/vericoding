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
/* helper modified by LLM (iteration 5): inductive proof that adding one element to a sequence adds its value to the sum */
lemma SumSeqAppendOneLemma(s: seq<real>, x: real)
  decreases |s|
  ensures SumSeq(s + [x]) == SumSeq(s) + x
{
  if |s| == 0 {
    assert s == [];
    assert SumSeq(s) == 0.0;
    assert SumSeq(s + [x]) == SumSeq([x]);
    assert SumSeq([x]) == [x][0] + SumSeq([x][1..]);
    assert [x][0] == x;
    assert [x][1..] == [];
    assert SumSeq([]) == 0.0;
  } else {
    var h := s[0];
    var t := s[1..];
    SumSeqAppendOneLemma(t, x);
    assert SumSeq(s + [x]) == (s + [x])[0] + SumSeq((s + [x])[1..]);
    assert (s + [x])[0] == h;
    assert (s + [x])[1..] == t + [x];
    assert SumSeq(s) == h + SumSeq(t);
    assert SumSeq(s + [x]) == h + SumSeq(t + [x]);
    assert SumSeq(t + [x]) == SumSeq(t) + x;
    assert SumSeq(s + [x]) == h + (SumSeq(t) + x);
    assert (h + SumSeq(t)) + x == h + (SumSeq(t) + x);
    assert SumSeq(s + [x]) == SumSeq(s) + x;
  }
}

/* helper modified by LLM (iteration 5): sequence prefix concatenated with the next element equals the next prefix */
lemma PrefixPlusElementEqualsNextPrefix<T>(s: seq<T>, i: nat)
  requires i < |s|
  ensures s[..i] + [s[i]] == s[..i+1]
{
  assert s[..i] + [s[i]] == s[..i+1];
}

/* helper modified by LLM (iteration 5): SumSeq respects sequence equality */
lemma SumSeqCongruence(s1: seq<real>, s2: seq<real>)
  requires s1 == s2
  ensures SumSeq(s1) == SumSeq(s2)
{
  // Follows by congruence of functions under equal arguments
}

/* helper modified by LLM (iteration 5): helper to relate GetDiagonal correctness for indexing */
lemma GetDiagonalIndex(matrix: seq<seq<real>>, n: nat, i: nat)
  requires n >= 0
  requires |matrix| == n
  requires forall j :: 0 <= j < n ==> |matrix[j]| == n
  requires i < n
  ensures GetDiagonal(matrix, n)[i] == matrix[i][i]
{
  // By definition of GetDiagonal
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
  /* code modified by LLM (iteration 5): compute the trace by summing the diagonal via a loop and connect it to SumSeq(GetDiagonal) */
  var n := |matrix|;
  var sum: real := 0.0;
  var i: nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |matrix| == n
    invariant forall j :: 0 <= j < n ==> |matrix[j]| == n
    invariant sum == SumSeq(GetDiagonal(matrix, n)[..i])
  {
    assert 0 <= i < n;
    GetDiagonalIndex(matrix, n, i);
    var diagVal := GetDiagonal(matrix, n)[i];
    sum := sum + diagVal;
    assert sum == SumSeq(GetDiagonal(matrix, n)[..i]) + GetDiagonal(matrix, n)[i];
    SumSeqAppendOneLemma(GetDiagonal(matrix, n)[..i], GetDiagonal(matrix, n)[i]);
    assert sum == SumSeq(GetDiagonal(matrix, n)[..i] + [GetDiagonal(matrix, n)[i]]);
    PrefixPlusElementEqualsNextPrefix(GetDiagonal(matrix, n), i);
    assert sum == SumSeq(GetDiagonal(matrix, n)[..i+1]);
    i := i + 1;
  }
  assert GetDiagonal(matrix, n)[..n] == GetDiagonal(matrix, n);
  SumSeqCongruence(GetDiagonal(matrix, n)[..n], GetDiagonal(matrix, n));
  assert SumSeq(GetDiagonal(matrix, n)[..n]) == SumSeq(GetDiagonal(matrix, n));
  result := sum;
}

// </vc-code>
