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
lemma SetSizeEqualsRange(start: int, end: int)
    requires start <= end
    ensures |set j {:trigger} | start <= j < end :: j| == end - start
    decreases end - start
{
    var indices := set j {:trigger} | start <= j < end :: j;
    if start == end {
        assert indices == {};
        assert |indices| == 0;
        assert end - start == 0;
    } else {
        assert start < end;
        var smaller := set j {:trigger} | start <= j < end - 1 :: j;
        SetSizeEqualsRange(start, end - 1);
        assert |smaller| == (end - 1) - start;
        assert indices == smaller + {end - 1};
        assert (end - 1) !in smaller;
        assert |indices| == |smaller| + 1;
        assert |indices| == ((end - 1) - start) + 1;
        assert |indices| == end - start;
    }
}

lemma ValueSetBoundedByIndexSet<T>(f: int -> T, start: int, end: int)
    requires start <= end
    ensures |set i | start <= i < end :: f(i)| <= |set i | start <= i < end :: i|
{
    var values := set i | start <= i < end :: f(i);
    var indices := set i | start <= i < end :: i;
    
    if start == end {
        assert values == {};
        assert indices == {};
        assert |values| == 0 && |indices| == 0;
    } else {
        assert forall v :: v in values ==> exists i :: start <= i < end && f(i) == v;
        assert forall v :: v in values ==> exists i :: i in indices && f(i) == v;
    }
}

lemma DistinctCountProperties(A: seq<int>, start: int)
    requires 0 <= start < |A|
    ensures DistinctCount(A, start) >= 0
    ensures DistinctCount(A, start) <= |A| - start
{
    var s := set j {:trigger A[j]} | start <= j < |A| :: A[j];
    var indices := set j {:trigger} | start <= j < |A| :: j;
    
    SetSizeEqualsRange(start, |A|);
    assert |indices| == |A| - start;
    
    ValueSetBoundedByIndexSet(i => A[i], start, |A|);
    assert |s| <= |indices|;
    assert |s| <= |A| - start;
}

lemma SetCardinality(A: seq<int>, start: int)
    requires 0 <= start < |A|
    ensures |set j {:trigger A[j]} | start <= j < |A| :: A[j]| == DistinctCount(A, start)
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

