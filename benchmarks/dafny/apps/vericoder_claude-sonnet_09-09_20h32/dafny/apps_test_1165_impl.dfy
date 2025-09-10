predicate ValidInput(n: int, m: int, A: seq<int>, queries: seq<(int, int, int)>)
{
    n > 0 && m >= 0 && |A| == n && |queries| == m &&
    forall q :: q in queries ==> 1 <= q.0 <= q.1 <= n
}

predicate ValidResult(A: seq<int>, queries: seq<(int, int, int)>, result: seq<int>)
{
    |result| == |queries| &&
    forall i :: 0 <= i < |queries| ==> (
        var l, r, x := queries[i].0, queries[i].1, queries[i].2;
        (result[i] == -1 ==> (forall j :: l <= j <= r ==> 0 <= j-1 < |A| && A[j-1] == x)) &&
        (result[i] != -1 ==> l <= result[i] <= r && 0 <= result[i]-1 < |A| && A[result[i]-1] != x)
    )
}

// <vc-helpers>
lemma IndexBoundsLemma(n: int, l: int, r: int, j: int)
    requires n > 0 && 1 <= l <= r <= n && l <= j <= r
    ensures 0 <= j-1 < n
{
}

lemma QueryValidityLemma(queries: seq<(int, int, int)>, i: int, n: int)
    requires 0 <= i < |queries|
    requires forall q :: q in queries ==> 1 <= q.0 <= q.1 <= n
    ensures var l, r, x := queries[i].0, queries[i].1, queries[i].2;
            1 <= l <= r <= n
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, A: seq<int>, queries: seq<(int, int, int)>) returns (result: seq<int>)
    requires ValidInput(n, m, A, queries)
    ensures ValidResult(A, queries, result)
// </vc-spec>
// <vc-code>
{
    result := [];
    var i := 0;
    
    while i < m
        invariant 0 <= i <= m
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> (
            var l, r, x := queries[k].0, queries[k].1, queries[k].2;
            (result[k] == -1 ==> (forall j {:trigger A[j-1]} :: l <= j <= r ==> 0 <= j-1 < |A| && A[j-1] == x)) &&
            (result[k] != -1 ==> l <= result[k] <= r && 0 <= result[k]-1 < |A| && A[result[k]-1] != x)
        )
    {
        var l, r, x := queries[i].0, queries[i].1, queries[i].2;
        QueryValidityLemma(queries, i, n);
        
        var found := false;
        var pos := -1;
        var j := l;
        
        while j <= r && !found
            invariant l <= j <= r + 1
            invariant !found ==> forall k {:trigger A[k-1]} :: l <= k < j ==> 0 <= k-1 < |A| && A[k-1] == x
            invariant found ==> l <= pos <= r && 0 <= pos-1 < |A| && A[pos-1] != x
        {
            IndexBoundsLemma(n, l, r, j);
            if A[j-1] != x {
                found := true;
                pos := j;
            }
            j := j + 1;
        }
        
        if found {
            result := result + [pos];
        } else {
            result := result + [-1];
        }
        
        i := i + 1;
    }
}
// </vc-code>

