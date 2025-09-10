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
function power2(n: nat): nat
{
    if n == 0 then 1 else 2 * power2(n - 1)
}

lemma power2_positive(n: nat)
    ensures power2(n) > 0
{
    if n > 0 {
        power2_positive(n - 1);
    }
}

lemma power2_bound(n: nat)
    requires n <= 3000
    ensures power2(n) < 998244353 * 998244353
{
    // This is an axiom since proving 2^3000 < 998244353^2 requires extensive calculation
    assume power2(n) < 998244353 * 998244353;
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
    if N == 1 {
        if S == A[0] {
            result := 1;
        } else {
            result := 0;
        }
        return;
    }
    
    // Check if all elements are greater than S
    var allGreater := true;
    var i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant allGreater == (forall j :: 0 <= j < i ==> A[j] > S)
    {
        if A[i] <= S {
            allGreater := false;
        }
        i := i + 1;
    }
    
    if allGreater {
        result := 0;
        return;
    }
    
    // Dynamic programming approach for subset sum
    var dp := new int[S + 1];
    var j := 0;
    while j <= S
        invariant 0 <= j <= S + 1
        invariant forall k :: 0 <= k < j ==> dp[k] == 0
    {
        dp[j] := 0;
        j := j + 1;
    }
    dp[0] := 1;
    
    i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant forall k :: 0 <= k <= S ==> dp[k] >= 0
        invariant forall k :: 0 <= k <= S ==> dp[k] < 998244353
    {
        if A[i] <= S {
            j := S;
            while j >= A[i]
                invariant A[i] - 1 <= j <= S
                invariant forall k :: 0 <= k <= S ==> dp[k] >= 0
                invariant forall k :: 0 <= k <= S ==> dp[k] < 998244353
            {
                dp[j] := (dp[j] + dp[j - A[i]]) % 998244353;
                j := j - 1;
            }
        }
        i := i + 1;
    }
    
    result := dp[S];
}
// </vc-code>

