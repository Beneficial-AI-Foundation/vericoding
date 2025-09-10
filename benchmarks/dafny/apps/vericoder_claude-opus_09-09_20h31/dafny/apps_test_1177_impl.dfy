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
function Power2Mod(n: nat): nat
    ensures Power2Mod(n) >= 0
    ensures Power2Mod(n) < 998244353
{
    if n == 0 then 1
    else (2 * Power2Mod(n - 1)) % 998244353
}

lemma Power2ModBounds(n: nat)
    ensures 0 <= Power2Mod(n) < 998244353
{
    // Proof by induction is automatic in Dafny
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
    
    // Dynamic programming approach to count subsequences that sum to S
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
        invariant forall k :: 0 <= k <= S ==> 0 <= dp[k] < 998244353
    {
        if A[i] <= S {
            j := S;
            while j >= A[i]
                invariant A[i] <= j + 1 <= S + 1
                invariant forall k :: 0 <= k <= S ==> 0 <= dp[k] < 998244353
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

