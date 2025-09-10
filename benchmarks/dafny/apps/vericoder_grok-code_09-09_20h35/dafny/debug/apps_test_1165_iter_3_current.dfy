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
{
    var res := [];
    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant |res| == i
        invariant forall k :: 0 <= k < i ==> (var l, r, x := queries[k].0, queries[k].1, queries[k].2; (res[k] == -1 ==> forall j :: l <= j <= r ==> A[j-1] == x) && (res[k] != -1 ==> l <= res[k] <= r && A[res[k]-1] != x))
    {
        var l := queries[i].0;
        var r := queries[i].1;
        var x := queries[i].2;
        var allEqual := true;
        var j := l;
        while j <= r && allEqual
            invariant l <= j <= r + 1
            invariant allEqual ==> forall k :: l <= k < j ==> A[k-1] == x
        {
            if A[j - 1] != x {
                allEqual := false;
            }
            j := j + 1;
        }
        var val : int;
        if allEqual {
            val := -1;
        } else {
            var firstDiff := l;
            j := l;
            while j <= r && A[j-1] == x
                invariant l <= j <= r + 1
                invariant forall k :: l <= k < j ==> A[k-1] == x
                invariant j > l ==> firstDiff == l  // since firstDiff is set to l initially and updated when != x
            {
                j := j + 1;
            }
            if j <= r {
                firstDiff := j;
            } else {
                // This shouldn't happen if allEqual is false, but to be safe
                firstDiff := r;
            }
            val := firstDiff;
        }
        res := res + [val];
        i := i + 1;
    }
    result := res;
}
// </vc-code>

