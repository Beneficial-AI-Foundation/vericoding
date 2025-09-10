predicate ValidInput(N: int, S: int, A: seq<int>)
{
    N >= 1 && S >= 1 && |A| == N && N <= 3000 && S <= 3000 &&
    forall i :: 0 <= i < N ==> A[i] >= 1 && A[i] <= 3000
}

predicate ValidResult(result: int)
{
    result >= 0 && result < 998244353
}

predicate AllElementsGreaterThanS(A: seq<int>, S: int)
{
    forall i :: 0 <= i < |A| ==> A[i] > S
}

function SingleElementCase(N: int, S: int, A: seq<int>): int
    requires N == 1 && |A| == 1
{
    if S == A[0] then 1 else 0
}

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(N: int, S: int, A: seq<int>) returns (result: int)
    requires ValidInput(N, S, A)
    ensures ValidResult(result)
    ensures result % 998244353 == result
    ensures (N == 1 && S == A[0]) ==> result == SingleElementCase(N, S, A)
    ensures (N == 1 && S != A[0]) ==> result == SingleElementCase(N, S, A)
    ensures AllElementsGreaterThanS(A, S) ==> result == 0
// </vc-spec>
// <vc-code>
{
  var dp := new int[S+1](_ => 0);
  dp[0] := 1;
  var i := 0;
  while i < N
    decreases N - i
    invariant 0 <= i <= N && forall k :: 0 <= k <= S ==> 0 <= dp[k] < 998244353
  {
    var a := A[i];
    if a <= S {
      var j := S;
      while j >= a
        decreases j
      {
        dp[j] = (dp[j] % 998244353 + dp[j - a] % 998244353) % 998244353;
        j := j - 1;
      }
    }
    i := i + 1;
  }
  result := dp[S];
}
// </vc-code>

