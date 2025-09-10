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
predicate IsSubsetSumPossible(A: seq<int>, S: int, index: int, currentSum: int)
{
    // Helper predicate to reason about subset sum possibilities
    index <= 0 || currentSum <= S
}

lemma SubsetSumLemma(A: seq<int>, S: int, n: int, k: int)
    requires 0 <= k <= n <= |A|
    requires S >= 0
    ensures true
{
}

ghost function CountSubsets(A: seq<int>, S: int, n: int): int
    decreases n
    requires 0 <= n <= |A|
    requires S >= 0
{
    if n == 0 then
        (if S == 0 then 1 else 0)
    else
        var prev := CountSubsets(A, S, n - 1);
        if S >= A[n-1] then
            prev + CountSubsets(A, S - A[n-1], n - 1)
        else
            prev
}

lemma CountSubsetsValid(A: seq<int>, S: int, n: int)
    requires 0 <= n <= |A|
    requires S >= 0
    ensures CountSubsets(A, S, n) >= 0 && CountSubsets(A, S, n) < 998244353
{
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
    var dp := new int[S+1];
    dp[0] := 1;
    var i: int := 0;
    while i < N
        invariant 0 <= i <= N
        invariant forall j :: 0 <= j <= S ==> dp[j] >= 0 && dp[j] < 998244353
        invariant dp[0] == 1
        decreases N - i
    {
        var temp := new int[S+1];
        temp := dp[..];
        
        var j: int := S;
        while j >= A[i]
            invariant j >= -1
            invariant forall k :: 0 <= k <= S ==> temp[k] >= 0 && temp[k] < 998244353
            decreases j + 1
        {
            if j - A[i] >= 0 {
                temp[j] := (temp[j] + dp[j - A[i]]) % 998244353;
            }
            j := j - 1;
        }
        
        dp := temp;
        i := i + 1;
    }
    
    result := dp[S];
}
// </vc-code>

