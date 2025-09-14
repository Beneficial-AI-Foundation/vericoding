predicate ValidInput(n: int, m: int, A: seq<int>, queries: seq<int>)
{
    |A| == n && |queries| == m && n >= 1 && m >= 1 &&
    forall i :: 0 <= i < m ==> 1 <= queries[i] <= n
}

function DistinctCount(A: seq<int>, start: int): int
    requires 0 <= start < |A|
{
    |set j | start <= j < |A| :: A[j]|
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, A: seq<int>, queries: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, m, A, queries)
    ensures |result| == m
    ensures forall i :: 0 <= i < m ==> 
        result[i] == DistinctCount(A, queries[i] - 1)
// </vc-spec>
// <vc-code>
{
    var ans := new int[m];
    for i := 0 to m
        invariant 0 <= i <= m
        invariant ans.Length == m
        invariant forall j :: 0 <= j < i ==> ans[j] == DistinctCount(A, queries[j] - 1)
    {
        ans[i] := DistinctCount(A, queries[i] - 1);
    }
    result := ans[..];
}
// </vc-code>

