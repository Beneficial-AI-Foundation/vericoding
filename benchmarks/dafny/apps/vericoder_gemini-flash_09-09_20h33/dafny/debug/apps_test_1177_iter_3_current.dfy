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
function sumSeq(s: seq<int>): int
  reads s
  decreases s
{
  if |s| == 0 then 0
  else s[0] + sumSeq(s[1..])
}
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
    var dp: array2<int>;
    var MOD: int := 998244353;

    if N == 1 {
        if S == A[0] then { return 1; } else { return 0; }
    }

    if AllElementsGreaterThanS(A, S) {
        return 0;
    }

    dp := new array2<int>(N + 1, S + 1);

    for i := 0 to N {
        for j := 0 to S {
            dp[i, j] := 0;
        }
    }

    // Base case: dp[0][0] = 1 (empty prefix, sum 0, one way)
    dp[0, 0] := 1;

    for i := 1 to N {
        for j := 0 to S {
            // Case 1: Don't include A[i-1] in the current sum
            dp[i, j] := (dp[i, j] + dp[i - 1, j]) % MOD;

            // Case 2: Include A[i-1] in the current sum, if possible
            if j - A[i-1] >= 0 {
                dp[i, j] := (dp[i, j] + dp[i - 1, j - A[i-1]]) % MOD;
            }
        }
    }

    result := 0;
    for j := 0 to S - 1 {
        result := (result + dp[N, j]) % MOD;
    }

    return result;
}
// </vc-code>

