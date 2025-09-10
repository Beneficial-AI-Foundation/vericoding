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
function computeDistinctCount(A: seq<int>, start: int): int
    requires 0 <= start <= |A|
    ensures computeDistinctCount(A, start) == DistinctCount(A, start)
{
    if start == |A| then
        0
    else
        var s := {};
        for i := start to |A| - 1
            invariant start <= i <= |A|
            invariant s == set j | start <= j < i :: A[j]
        {
            s := s + {A[i]};
        }
        |s|
}

// Ensure there's only one definition of DistinctCount
// function DistinctCount(A: seq<int>, start: int): int
//    requires 0 <= start <= |A|
// {
//    |set j | start <= j < |A| :: A[j]|
// }
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
    var result: seq<int> := new seq<int>(m, _ => 0);
    for i := 0 to m - 1
        invariant 0 <= i <= m
        invariant forall k :: 0 <= k < i ==> result[k] == DistinctCount(A, queries[k] - 1)
    {
        var startIndex := queries[i] - 1;
        result := result[i := computeDistinctCount(A, startIndex)];
    }
    return result;
}
// </vc-code>

