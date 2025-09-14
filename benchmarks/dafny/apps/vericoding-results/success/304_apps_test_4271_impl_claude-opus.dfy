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
lemma SumSatisfactionInductive(A: seq<int>, B: seq<int>, C: seq<int>, k: int)
    requires 0 <= k < |A|
    requires |B| == |A|
    requires |C| == |A| - 1
    requires forall i :: 0 <= i < |A| ==> 1 <= A[i] <= |A|
    ensures SumSatisfactionUpTo(A, B, C, k + 1) == 
            SumSatisfactionUpTo(A, B, C, k) + B[A[k] - 1] + 
            (if k > 0 && A[k] == A[k-1] + 1 then C[A[k] - 2] else 0)
{
    // This follows directly from the function definition
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, A: seq<int>, B: seq<int>, C: seq<int>) returns (result: int)
    requires ValidInput(N, A, B, C)
    ensures result == SumSatisfaction(A, B, C, N)
// </vc-spec>
// <vc-code>
{
    result := 0;
    var i := 0;
    
    while i < N
        invariant 0 <= i <= N
        invariant result == SumSatisfactionUpTo(A, B, C, i)
    {
        var baseContrib := B[A[i] - 1];
        var bonusContrib := if i > 0 && A[i] == A[i-1] + 1 then C[A[i] - 2] else 0;
        result := result + baseContrib + bonusContrib;
        
        SumSatisfactionInductive(A, B, C, i);
        i := i + 1;
    }
}
// </vc-code>

