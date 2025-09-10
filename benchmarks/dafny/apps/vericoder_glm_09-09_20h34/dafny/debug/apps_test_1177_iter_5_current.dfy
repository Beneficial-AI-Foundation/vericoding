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
lemma ModuloPreservesNonNegativity(x: int, y: int)
    requires x >= 0 && y > 0
    ensures x % y >= 0
{
    calc {
        x % y;
        x - (x / y) * y;
        >= { assert (x / y) * y <= x; } 
        0;
    }
}

lemma ModuloPreservesUpperBound(x: int, y: int)
    requires x >= 0 && y > 0
    ensures x % y < y
{
    calc {
        x % y;
        x - (x / y) * y;
        < { assert (x / y + 1) * y > x; }
        y;
    }
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
    for i := 0 to N-1
        invariant dp[0] == 1;
        invariant forall j :: 1 <= j <= S ==> dp[j] >= 0 && dp[j] < 998244353;
    {
        var a := A[i];
        if a <= S {
            var j := S;
            while j >= a
                invariant dp[0] == 1;
                invariant forall k :: 1 <= k <= S ==> dp[k] >= 0 && dp[k] < 998244353;
            {
                var new_val := dp[j] + dp[j - a];
                ModuloPreservesNonNegativity(new_val, 998244353);
                ModuloPreservesUpperBound(new_val, 998244353);
                dp[j] := new_val % 998244353;
                j := j - 1;
            }
        }
    }
    result := dp[S];
}
// </vc-code>

