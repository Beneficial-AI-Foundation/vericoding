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
lemma DistinctCountProperties(A: seq<int>, start: int)
    requires 0 <= start < |A|
    ensures DistinctCount(A, start) >= 0
    ensures DistinctCount(A, start) <= |A| - start
{
    var s := set j | start <= j < |A| :: A[j];
    var indices := set j | start <= j < |A| :: j;
    assert |indices| == |A| - start;
    
    // Each element in s comes from some index in the range [start, |A|)
    assert forall v :: v in s ==> exists k :: start <= k < |A| && A[k] == v;
    
    // The mapping from indices to values shows that |s| <= |indices|
    assert s == set k | k in indices :: A[k];
    assert |s| <= |indices|;
    assert |s| <= |A| - start;
}

lemma SetCardinality(A: seq<int>, start: int)
    requires 0 <= start < |A|
    ensures |set j | start <= j < |A| :: A[j]| == DistinctCount(A, start)
{
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
        var queryIndex := queries[i] - 1;
        assert 0 <= queryIndex < n by {
            assert 1 <= queries[i] <= n;
        }
        assert 0 <= queryIndex < |A|;
        
        var distinctCount := DistinctCount(A, queryIndex);
        DistinctCountProperties(A, queryIndex);
        
        result := result + [distinctCount];
        i := i + 1;
    }
}
// </vc-code>

