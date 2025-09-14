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
lemma ValidResultProperty(A: seq<int>, queries: seq<(int, int, int)>, result: seq<int>, i: int)
    requires |result| == |queries|
    requires 0 <= i < |queries|
    requires var l, r, x := queries[i].0, queries[i].1, queries[i].2;
             (result[i] == -1 ==> (forall j :: l <= j <= r ==> 0 <= j-1 < |A| && A[j-1] == x)) &&
             (result[i] != -1 ==> l <= result[i] <= r && 0 <= result[i]-1 < |A| && A[result[i]-1] != x)
    ensures ValidResult(A, queries, result) ==> 
            (var l, r, x := queries[i].0, queries[i].1, queries[i].2;
             (result[i] == -1 ==> (forall j :: l <= j <= r ==> 0 <= j-1 < |A| && A[j-1] == x)) &&
             (result[i] != -1 ==> l <= result[i] <= r && 0 <= result[i]-1 < |A| && A[result[i]-1] != x))
{
}

lemma AllElementsEqualImpliesForall(A: seq<int>, l: int, r: int, x: int)
    requires 1 <= l <= r <= |A|
    requires forall k :: l <= k <= r ==> 0 <= k-1 < |A| && A[k-1] == x
    ensures forall j :: l <= j <= r ==> 0 <= j-1 < |A| && A[j-1] == x
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
    var queryIndex := 0;
    
    while queryIndex < m
        invariant 0 <= queryIndex <= m
        invariant |result| == queryIndex
        invariant forall i :: 0 <= i < queryIndex ==> (
            var l, r, x := queries[i].0, queries[i].1, queries[i].2;
            (result[i] == -1 ==> (forall j :: l <= j <= r ==> 0 <= j-1 < |A| && A[j-1] == x)) &&
            (result[i] != -1 ==> l <= result[i] <= r && 0 <= result[i]-1 < |A| && A[result[i]-1] != x)
        )
    {
        var l, r, x := queries[queryIndex].0, queries[queryIndex].1, queries[queryIndex].2;
        assert 1 <= l <= r <= n;
        assert |A| == n;
        var found := -1;
        var j := l;
        
        while j <= r && found == -1
            invariant l <= j <= r + 1
            invariant found == -1 || (l <= found <= r && 0 <= found-1 < |A| && A[found-1] != x)
            invariant found == -1 ==> (forall k :: l <= k < j ==> 0 <= k-1 < |A| && A[k-1] == x)
            decreases if found == -1 then r - j + 1 else 0
        {
            if A[j-1] != x {
                found := j;
            } else {
                j := j + 1;
            }
        }
        
        assert found == -1 ==> j == r + 1;
        
        if found == -1 {
            assert forall k :: l <= k <= r ==> 0 <= k-1 < |A| && A[k-1] == x;
            AllElementsEqualImpliesForall(A, l, r, x);
        }
        
        result := result + [found];
        queryIndex := queryIndex + 1;
    }
}
// </vc-code>

