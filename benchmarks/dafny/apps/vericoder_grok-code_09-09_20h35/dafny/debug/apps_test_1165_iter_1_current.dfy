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
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, A: seq<int>, queries: seq<(int, int, int)>) returns (result: seq<int>)
    requires ValidInput(n, m, A, queries)
    ensures ValidResult(A, queries, result)
// </vc-spec>
// <vc-code>
var res := [];
    for i := 0 to m-1 {
        var l := queries[i].0;
        var r := queries[i].1;
        var x := queries[i].2;
        var allEqual := true;
        for j := l to r {
            if A[j-1] != x {
                allEqual := false;
                break;
            }
        }
        var val := if allEqual then -1 else (
            var firstDiff := l;
            for j := l to r {
                if A[j-1] != x {
                    firstDiff := j;
                    break;
                }
            }
            firstDiff
        );
        res := res + [val];
    }
    result := res;
// </vc-code>

