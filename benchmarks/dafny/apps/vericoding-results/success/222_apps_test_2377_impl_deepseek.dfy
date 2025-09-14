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
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures sumSeq(s) > 0
{
  if |s| == 1 {
    assert sumSeq(s) == s[0] > 0;
  } else {
    assert s[0] > 0;
    sumSeqProperties(s[1..]);
    assert sumSeq(s) == s[0] + sumSeq(s[1..]) > 0;
  }
}

lemma maxExists(A: seq<int>)
  requires |A| > 0
  ensures exists maxA :: maxA in A && (forall i :: 0 <= i < |A| ==> A[i] <= maxA)
{
  if |A| == 1 {
    var single := A[0];
    assert single in A;
    assert forall i :: 0 <= i < |A| ==> A[i] <= single;
  } else {
    var head := A[0];
    var tail := A[1..];
    maxExists(tail);
    var tailMax :| tailMax in tail && (forall i :: 0 <= i < |tail| ==> tail[i] <= tailMax);
    if head > tailMax {
      assert head in A;
      assert forall i :: 0 <= i < |A| ==> A[i] <= head;
    } else {
      assert tailMax in A;
      assert forall i :: 0 <= i < |A| ==> A[i] <= tailMax;
    }
  }
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
  var i := 1;
  
  assert maxA in A[0..1];
  assert forall j :: 0 <= j < 1 ==> A[j] <= maxA;
  
  while i < N
    invariant 1 <= i <= N
    invariant maxA in A[0..i]
    invariant forall j :: 0 <= j < i ==> A[j] <= maxA
  {
    if A[i] > maxA {
      maxA := A[i];
    }
    assert A[i] <= maxA;
    i := i + 1;
  }
  
  // Proof that result is positive
  assert maxA > 0 by {
    assert maxA in A;
    assert forall k :: 0 <= k < N ==> A[k] > 0;
  }
  
  result := maxA;
}
// </vc-code>

