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
method CountDistinctFrom(A: seq<int>, start: int) returns (cnt: int)
    requires 0 <= start < |A|
    ensures cnt == DistinctCount(A, start)
{
    var seen: set<int> := {};
    var j := start;
    while j < |A|
        invariant start <= j <= |A|
        invariant seen == set k | start <= k < j :: A[k]
        decreases |A| - j
    {
        if A[j] !in seen {
            seen := seen + {A[j]};
        }
        j := j + 1;
    }
    cnt := |seen|;
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
    var res: seq<int> := [];
    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant |res| == i
        invariant forall t :: 0 <= t < i ==> res[t] == DistinctCount(A, queries[t] - 1)
        decreases m - i
    {
        var start := queries[i] - 1;
        var c := CountDistinctFrom(A, start);
        res := res + [c];
        i := i + 1;
    }
    result := res;
}
// </vc-code>

