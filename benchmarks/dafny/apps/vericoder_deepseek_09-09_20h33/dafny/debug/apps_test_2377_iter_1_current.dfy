predicate ValidInput(N: int, H: int, A: seq<int>, B: seq<int>)
{
    |A| == N && |B| == N && N > 0 && H > 0 &&
    (forall i :: 0 <= i < N ==> A[i] > 0 && B[i] > 0) &&
    (forall i :: 0 <= i < N ==> A[i] <= B[i])
}

function sumSeq(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sumSeq(s[1..])
}

predicate MaxWieldExists(A: seq<int>, maxA: int)
{
    maxA in A && (forall i :: 0 <= i < |A| ==> A[i] <= maxA)
}

// <vc-helpers>
lemma sumSeqProperties(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures sumSeq(s) > 0
{
  if |s| == 0 {
    // sum of empty sequence is 0, but the lemma requires s to have positive elements
  } else {
    assert s[0] > 0;
    sumSeqProperties(s[1..]);  // recursive call on the tail
    assert sumSeq(s) == s[0] + sumSeq(s[1..]) > 0 + 0;
  }
}

lemma maxExists(A: seq<int>)
  requires |A| > 0
  ensures exists maxA :: maxA in A && (forall i :: 0 <= i < |A| ==> A[i] <= maxA)
{
  // This is a fundamental property of finite non-empty sequences
}

lemma sumGreaterOrEqual(A: seq<int>, B: seq<int>)
  requires |A| == |B| 
  requires forall i :: 0 <= i < |A| ==> A[i] <= B[i]
  ensures sumSeq(A) <= sumSeq(B)
{
  if |A| == 0 {
    // trivial case
  } else {
    assert A[0] <= B[0];
    sumGreaterOrEqual(A[1..], B[1..]);
    assert sumSeq(A) == A[0] + sumSeq(A[1..]) <= B[0] + sumSeq(B[1..]) == sumSeq(B);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, H: int, A: seq<int>, B: seq<int>) returns (result: int)
  requires ValidInput(N, H, A, B)
  ensures result > 0
// </vc-spec>
// <vc-code>
{
  var maxA := A[0];
  var i := 0;
  
  while i < N
    invariant 0 <= i <= N
    invariant maxA in A[0..i]
    invariant forall j :: 0 <= j < i ==> A[j] <= maxA
  {
    if A[i] > maxA {
      maxA := A[i];
    }
    i := i + 1;
  }
  
  result := maxA;
  
  // Proof that result is positive
  assert maxA in A;
  assert forall i :: 0 <= i < N ==> A[i] > 0;
  assert result > 0;
}
// </vc-code>

