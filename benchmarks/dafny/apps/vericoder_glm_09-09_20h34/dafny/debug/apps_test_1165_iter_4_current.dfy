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
method FindIndex(l: int, r: int, x: int, A: seq<int>) returns (res: int)
    requires 1 <= l <= r <= |A|
    ensures res == -1 || (l <= res <= r && 0 <= res-1 < |A| && A[res-1] != x)
    ensures res == -1 <==> forall j :: l <= j <= r ==> A[j-1] == x
{
    var j := l-1;
    while j <= r-1
        invariant l-1 <= j <= r
        invariant forall k :: l-1 <= k < j ==> 0 <= k < |A| && A[k] == x
    {
        if A[j] != x {
            return j+1;
        }
        j := j+1;
    }
    return -1;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, A: seq<int>, queries: seq<(int, int, int)>) returns (result: seq<int>)
    requires ValidInput(n, m, A, queries)
    ensures ValidResult(A, queries, result)
// </vc-spec>
// <vc-code>
{
    var result := new int[m];
    for i := 0 to m-1
        invariant 0 <= i <= m
        invariant |result| == m
        invariant forall j :: 0 <= j < i ==> ValidResult(A, [queries[k] for k in 0..j], [result[k] for k in 0..j])
    {
        var (l, r, x) := queries[i];
        result[i] := FindIndex(l, r, x, A);
    }
    return result;
}
// </vc-code>

