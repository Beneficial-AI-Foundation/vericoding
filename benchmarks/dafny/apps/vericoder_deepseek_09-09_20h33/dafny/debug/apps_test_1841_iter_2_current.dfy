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
lemma DistinctCountLemma(A: seq<int>, start: int, end: int)
    requires 0 <= start <= end <= |A|
    ensures DistinctCount(A, start) == DistinctCount(A, end) + |set j | start <= j < end :: A[j]|
    decreases end - start
{
    if start == end {
    } else {
        DistinctCountLemma(A, start, end - 1);
    }
}

function CountDistinctInRange(A: seq<int>, start: int, end: int): int
    requires 0 <= start <= end <= |A|
{
    |set j | start <= j < end :: A[j]|
}

lemma DistinctCountDecomposition(A: seq<int>, start: int, mid: int, end: int)
    requires 0 <= start <= mid <= end <= |A|
    ensures DistinctCount(A, start) == DistinctCount(A, mid) + CountDistinctInRange(A, start, mid)
{
    DistinctCountLemma(A, start, mid);
}

lemma DistinctCountEquivalence(A: seq<int>, start: int)
    requires 0 <= start < |A|
    ensures DistinctCount(A, start) == CountDistinctInRange(A, start, |A|)
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
    var distinctFromEnd := new int[n];
    var seen: set<int> := {};
    
    for i := n - 1 downto 0
        invariant i >= -1 && i < n
        invariant distinctFromEnd.Length == n
        invariant forall j :: i < j < n ==> distinctFromEnd[j] == |set k | j <= k < n :: A[k]|
    {
        seen := seen + {A[i]};
        distinctFromEnd[i] := |seen|;
    }
    
    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == DistinctCount(A, queries[j] - 1)
    {
        var idx := queries[i] - 1;
        result := result + [distinctFromEnd[idx]];
        i := i + 1;
    }
}
// </vc-code>

