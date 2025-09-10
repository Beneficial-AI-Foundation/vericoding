predicate ValidInput(N: int, A: seq<int>, B: seq<int>, C: seq<int>)
{
    N >= 1 &&
    |A| == N &&
    |B| == N &&
    |C| == N - 1 &&
    (forall i :: 0 <= i < N ==> 1 <= A[i] <= N) &&
    (forall i, j :: 0 <= i < j < N ==> A[i] != A[j])
}

function SumSatisfaction(A: seq<int>, B: seq<int>, C: seq<int>, N: int): int
    requires N >= 1
    requires |A| == N
    requires |B| == N
    requires |C| == N - 1
    requires forall i :: 0 <= i < N ==> 1 <= A[i] <= N
{
    SumSatisfactionUpTo(A, B, C, N)
}

function SumSatisfactionUpTo(A: seq<int>, B: seq<int>, C: seq<int>, k: int): int
    requires 0 <= k <= |A|
    requires |B| == |A|
    requires |C| == |A| - 1
    requires forall i :: 0 <= i < |A| ==> 1 <= A[i] <= |A|
{
    if k == 0 then 0
    else
        var prevSum := SumSatisfactionUpTo(A, B, C, k-1);
        var baseContrib := B[A[k-1] - 1];
        var bonusContrib := if k > 1 && A[k-1] == A[k-2] + 1 then C[A[k-1] - 2] else 0;
        prevSum + baseContrib + bonusContrib
}

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
method solve(N: int, A: seq<int>, B: seq<int>, C: seq<int>) returns (result: int)
    requires ValidInput(N, A, B, C)
    ensures result == SumSatisfaction(A, B, C, N)
// </vc-spec>
// <vc-code>
{
  var sum := 0;
  var prevA := 0; // dummy value
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant sum == SumSatisfactionUpTo(A, B, C, i)
    invariant i > 0 ==> prevA == A[i - 1]
  {
    var contrib := B[A[i] - 1];
    sum := sum + contrib;
    if i >= 1 && A[i] == prevA + 1 {
      sum := sum + C[A[i] - 2];
    }
    prevA := A[i];
    i := i + 1;
  }
  result := sum;
}
// </vc-code>

