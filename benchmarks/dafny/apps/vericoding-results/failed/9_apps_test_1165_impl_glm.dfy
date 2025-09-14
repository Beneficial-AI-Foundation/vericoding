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
predicate ValidResultForQuery(A: seq<int>, query: (int, int, int), res: int)
{
    var l, r, x := query.0, query.1, query.2;
    (res == -1 ==> (forall j {:trigger A[j-1]} :: l <= j <= r ==> 0 <= j-1 < |A| && A[j-1] == x)) &&
    (res != -1 ==> l <= res <= r && 0 <= res-1 < |A| && A[res-1] != x)
}

predicate ValidResult(A: seq<int>, queries: seq<(int, int, int)>, result: seq<int>)
{
    |result| == |queries| &&
    forall i :: 0 <= i < |queries| ==> ValidResultForQuery(A, queries[i], result[i])
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
    while i < |queries|
        invariant 0 <= i <= |queries|
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> ValidResultForQuery(A, queries[k], result[k])
    {
        var q := queries[i];
        var l, r, x := q.0, q.1, q.2;
        var j := l;
        while j <= r
            invariant l <= j <= r+1
            invariant forall k {:trigger A[k-1]} :: l <= k < j ==> A[k-1] == x
        {
            if A[j-1] != x {
                break;
            }
            j := j + 1;
        }
        if j <= r {
            result := result + [j];
        } else {
            result := result + [-1];
        }
        i := i + 1;
    }
}
// </vc-code>

