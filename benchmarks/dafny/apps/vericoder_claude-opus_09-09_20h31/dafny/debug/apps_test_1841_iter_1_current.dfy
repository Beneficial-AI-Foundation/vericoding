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
method ComputeDistinct(A: seq<int>, start: int) returns (count: int)
    requires 0 <= start < |A|
    ensures count == DistinctCount(A, start)
{
    var seen: set<int> := {};
    var i := start;
    
    while i < |A|
        invariant start <= i <= |A|
        invariant seen == set j | start <= j < i :: A[j]
    {
        seen := seen + {A[i]};
        i := i + 1;
    }
    
    assert seen == set j | start <= j < |A| :: A[j];
    count := |seen|;
}
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
    result := [];
    var i := 0;
    
    while i < m
        invariant 0 <= i <= m
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> result[k] == DistinctCount(A, queries[k] - 1)
    {
        var distinctCount := ComputeDistinct(A, queries[i] - 1);
        result := result + [distinctCount];
        i := i + 1;
    }
}
// </vc-code>

