// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(N: int, H: int, A: seq<int>, B: seq<int>) returns (result: int)
  requires ValidInput(N, H, A, B)
  ensures result > 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
